-- Prove2me | solution 1 for Rigidity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:27:57.216931+00:00
-- url     : https://prove2.me/submissions/78eae8c8-3db9-4aa0-b12f-6fb979867a40

import Definitions.Def_PHigherOrder_BlowupUniformConvergence
import Definitions.Def_PHigherOrder_PHarmGradientCompactness
import Definitions.Def_PHigherOrder_PHarmUnionExhaustion
import Definitions.Def_PHigherOrder_PHarmLimit
import Definitions.Def_PHigherOrder_LewisRigidityInput
import Definitions.Def_PHigherOrder_Rigidity
import Theorems.Thm_BlowupUniformConvergence
import Theorems.Thm_PHarmGradientCompactness
import Theorems.Thm_PHarmLimit
import Theorems.Thm_PHarmNormalize
import Theorems.Thm_PHarmRestrict
import Theorems.Thm_PHarmUnionExhaustion


set_option autoImplicit false

theorem _root_.solution (p : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hL : LewisRigidityInput p) (F : FirstOrderEstimateInput p)
    (Ω : Set Plane) (u : Plane → ℝ) (x₀ : Plane) (hx₀ : x₀ ∈ Ω)
    (m : ℕ) (hm : 2 ≤ m)
    (hu : ContDiffOn ℝ (m : ℕ∞) u Ω)
    (hph : IsPHarm p Ω u (gradient u))
    (hcrit : gradient u x₀ = 0) :
    ∀ j, 2 ≤ j → j ≤ m → ∀ w : Plane, iteratedFDeriv ℝ j u x₀ (fun _ => w) = 0 := by
  have hOopen : IsOpen Ω := hph.openOmega
  obtain ⟨ρ, hρ, hρsub⟩ : ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball x₀ ρ ⊆ Ω :=
    let ⟨ρ, hρ, h⟩ := Metric.isOpen_iff.mp hOopen x₀ hx₀; ⟨ρ, hρ, h⟩
  have hballharm : IsPHarm p (Metric.ball x₀ ρ) u (gradient u) :=
    (PHarmRestrict p hp hp2 Ω u (gradient u) hph).1 _ Metric.isOpen_ball hρsub
  have hx₀ball : x₀ ∈ Metric.ball x₀ ρ := Metric.mem_ball_self hρ
  have huball : ContDiffOn ℝ (m : ℕ∞) u (Metric.ball x₀ ρ) := hu.mono hρsub
  have hudiff : ∀ y ∈ Ω, DifferentiableAt ℝ u y := by
    intro y hy
    exact ((hu.differentiableOn (by exact_mod_cast (by omega : m ≠ 0))) y
      hy).differentiableAt (hOopen.mem_nhds hy)
  -- The induction is run on the shifted, order-quantified statement `T q`.
  have T : ∀ q : ℕ, q ≤ m + 1 → ∀ j, 1 ≤ j → j < q →
      ∀ w : Plane, iteratedFDeriv ℝ j u x₀ (fun _ => w) = 0 := by
    intro q
    induction q with
    | zero => intro _ j _ hj; omega
    | succ q ih =>
    intro hq j hj1 hjq w
    rcases Nat.lt_succ_iff_lt_or_eq.mp hjq with hlt | heq
    · exact ih (by omega) j hj1 hlt w
    -- `j = q`, so `1 ≤ j ≤ m` and the inductive hypothesis is the vanishing below `j`.
    have hT : ∀ j', 1 ≤ j' → j' < j → ∀ w' : Plane,
        iteratedFDeriv ℝ j' u x₀ (fun _ => w') = 0 := fun j' h1 h2 => ih (by omega) j' h1 (by omega)
    have hjm : j ≤ m := by omega
    rcases Nat.lt_or_ge j 2 with hjlt | hj2
    · -- Base case `j = 1`: the critical-point hypothesis.
      have hj1' : j = 1 := by omega
      subst hj1'
      rw [iteratedFDeriv_one_apply, ← inner_gradient_left (𝕜 := ℝ), hcrit, inner_zero_left]
    -- Blow-up argument for `2 ≤ j ≤ m`.
    let P : Plane → ℝ := fun x => (1 / (Nat.factorial j : ℝ)) * iteratedFDeriv ℝ j u x₀ (fun _ => x)
    let Q : ContinuousMultilinearMap ℝ (fun _ : Fin j => Plane) ℝ :=
      (1 / (Nat.factorial j : ℝ)) • iteratedFDeriv ℝ j u x₀
    let r : ℕ → ℝ := fun n => ρ / ((n : ℝ) + 1)
    let v : ℕ → Plane → ℝ := fun n x => (u (x₀ + r n • x) - u x₀) / r n ^ j
    let gg : ℕ → Plane → Plane := fun n x => (r n / r n ^ j) • gradient u (x₀ + r n • x)
    let Ωn : ℕ → Set Plane := fun n => Metric.ball (0 : Plane) ((n : ℝ) + 1)
    have hn1 : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
    have hrdef : ∀ n : ℕ, r n = ρ / ((n : ℝ) + 1) := fun n => rfl
    have hΩndef : ∀ n : ℕ, Ωn n = Metric.ball (0 : Plane) ((n : ℝ) + 1) := fun n => rfl
    have hrpos : ∀ n, 0 < r n := fun n => div_pos hρ (hn1 n)
    -- Step 1 + 2: the blow-ups are `p`-harmonic on balls that exhaust the plane.
    have hset : ∀ n : ℕ, {x : Plane | x₀ + r n • x ∈ Metric.ball x₀ ρ} = Ωn n := by
      intro n
      rw [hΩndef n]
      ext x
      simp only [Set.mem_ofPred_eq, Metric.mem_ball, dist_eq_norm, add_sub_cancel_left,
        sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos (hrpos n)]
      rw [hrdef n, div_mul_eq_mul_div, div_lt_iff₀ (hn1 n)]
      constructor
      · intro h; nlinarith
      · intro h; nlinarith
    have hvharm : ∀ n, IsPHarm p (Ωn n) (v n) (gg n) := by
      intro n
      have h := PHarmNormalize p hp hp2 (Metric.ball x₀ ρ) u (gradient u) x₀ (r n)
        (r n ^ j) (u x₀) (hrpos n) (by positivity) hballharm
      rwa [hset n] at h
    have hmonoΩ : Monotone Ωn := by
      intro a b hab
      refine Metric.ball_subset_ball ?_
      have : (a : ℝ) ≤ (b : ℝ) := Nat.cast_le.mpr hab
      linarith
    have hunion : (⋃ n, Ωn n) = Set.univ := by
      refine Set.eq_univ_of_forall fun z => ?_
      obtain ⟨n, hn⟩ := exists_nat_gt ‖z‖
      refine Set.mem_iUnion.mpr ⟨n, ?_⟩
      rw [hΩndef n]
      simp only [Metric.mem_ball, dist_zero_right]
      linarith
    -- Step 3: the `C^0` convergence, read off BlowupUniformConvergence along `r n → 0⁺`.
    have hrlim : Filter.Tendsto r Filter.atTop (nhdsWithin 0 (Set.Ioi (0 : ℝ))) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, Filter.Eventually.of_forall fun n => Set.mem_Ioi.mpr (hrpos n)⟩
      have h0 : Filter.Tendsto (fun n : ℕ => ρ * (1 / ((n : ℝ) + 1))) Filter.atTop
          (nhds (ρ * 0)) :=
        (tendsto_const_nhds (x := ρ) (f := Filter.atTop (α := ℕ))).mul
          tendsto_one_div_add_atTop_nhds_zero_nat
      rw [mul_zero] at h0
      exact h0.congr fun n => by rw [mul_one_div]
    have hC0 : ∀ R : ℝ, 0 < R →
        TendstoUniformlyOn v P Filter.atTop (Metric.closedBall (0 : Plane) R) := by
      intro R hR
      have hBU := BlowupUniformConvergence (Metric.ball x₀ ρ) Metric.isOpen_ball u x₀ hx₀ball
        j (by omega) (huball.of_le (by exact_mod_cast hjm)) (fun j' h1 h2 w' => hT j' h1 h2 w') R hR
      rw [Metric.tendstoUniformlyOn_iff] at hBU ⊢
      exact fun ε hε => hrlim.eventually (hBU ε hε)
    -- Step 4: eventual local uniform boundedness, from the polynomial's own bound.
    have hbd : ∀ K : Set Plane, K ⊆ (⋃ n, Ωn n) → IsCompact K →
        ∃ M : ℝ, 0 < M ∧ ∃ N : ℕ, ∀ n, N ≤ n → ∀ z ∈ K, |v n z| ≤ M := by
      intro K _ hKc
      obtain ⟨R0, hR0⟩ := hKc.isBounded.subset_closedBall (0 : Plane)
      have hR : (0 : ℝ) < max R0 1 := by positivity
      have hKR : K ⊆ Metric.closedBall (0 : Plane) (max R0 1) :=
        hR0.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
        (Metric.tendstoUniformlyOn_iff.mp (hC0 (max R0 1) hR) 1 one_pos)
      refine ⟨‖Q‖ * (max R0 1) ^ j + 2, by positivity, N, ?_⟩
      intro n hn z hz
      have hPz : |P z| ≤ ‖Q‖ * (max R0 1) ^ j := by
        have hzR : ‖z‖ ≤ max R0 1 := by
          have := hKR hz; simpa using this
        have h2 : ‖Q (fun _ => z)‖ ≤ ‖Q‖ * (max R0 1) ^ j :=
          Q.le_opNorm_mul_pow_of_le
            ((pi_norm_le_iff_of_nonneg (le_trans (norm_nonneg z) hzR)).mpr fun _ => hzR)
        have h3 : Q (fun _ => z) = P z := by simp [Q, P]
        rwa [h3, Real.norm_eq_abs] at h2
      have h1 : dist (P z) (v n z) < 1 := hN n hn z (hKR hz)
      rw [Real.dist_eq] at h1
      have h4 := abs_sub_abs_le_abs_sub (v n z) (P z)
      rw [abs_sub_comm] at h4
      linarith
    -- Step 5: one subsequence carrying both convergences.
    obtain ⟨-, φ, hφ, V, G, hVconv, hGconv⟩ :=
      PHarmGradientCompactness p hp hp2 F Ωn hmonoΩ v gg hvharm hbd
    -- `gg n` is the classical gradient of `v n` on `Ωn n` (the affine chain rule).
    have hgrad : ∀ n, Set.EqOn (gg n) (fun x => gradient (v n) x) (Ωn n) := by
      intro n x hx
      have hmem : x₀ + r n • x ∈ Metric.ball x₀ ρ := by
        have : x ∈ {y : Plane | x₀ + r n • y ∈ Metric.ball x₀ ρ} := by rw [hset n]; exact hx
        exact this
      have hrne : r n ≠ 0 := ne_of_gt (hrpos n)
      have hjne : (r n ^ j) ≠ 0 := pow_ne_zero _ hrne
      have hTd : HasFDerivAt (fun y : Plane => x₀ + r n • y)
          (r n • ContinuousLinearMap.id ℝ Plane) x :=
        ((hasFDerivAt_id x).const_smul (r n)).const_add x₀
      have hud : HasFDerivAt u (fderiv ℝ u (x₀ + r n • x)) (x₀ + r n • x) :=
        (hudiff _ (hρsub hmem)).hasFDerivAt
      have hcomp : HasFDerivAt (fun y : Plane => u (x₀ + r n • y))
          ((fderiv ℝ u (x₀ + r n • x)).comp (r n • ContinuousLinearMap.id ℝ Plane)) x :=
        hud.comp x hTd
      have hvd : HasFDerivAt (v n)
          ((1 / r n ^ j) • ((fderiv ℝ u (x₀ + r n • x)).comp
            (r n • ContinuousLinearMap.id ℝ Plane))) x := by
        have h := (hcomp.sub_const (u x₀)).const_smul (1 / r n ^ j)
        refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
        show (u (x₀ + r n • y) - u x₀) / r n ^ j = (1 / r n ^ j) • (u (x₀ + r n • y) - u x₀)
        rw [smul_eq_mul, one_div, inv_mul_eq_div]
      have hfd : fderiv ℝ (v n) x = (r n / r n ^ j) • fderiv ℝ u (x₀ + r n • x) := by
        rw [hvd.fderiv]
        ext z
        simp only [smul_apply, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
        ring
      show gg n x = gradient (v n) x
      refine ((InnerProductSpace.toDual ℝ Plane).injective ?_).symm
      rw [toDual_gradient, hfd, map_smul, toDual_gradient]
    -- Steps 7 and 8: `P` is `p`-harmonic on each ball, hence on the plane.
    have hPharmball : ∀ n : ℕ, IsPHarm p (Ωn n) P G := by
      intro n
      have hsub : ∀ i : ℕ, Ωn n ⊆ Ωn (φ (i + (n + 1))) := by
        intro i
        refine hmonoΩ ?_
        have h1 : i + (n + 1) ≤ φ (i + (n + 1)) := hφ.le_apply
        omega
      have hshift : Filter.Tendsto (fun i => φ (i + (n + 1))) Filter.atTop Filter.atTop :=
        hφ.tendsto_atTop.comp (Filter.tendsto_add_atTop_nat (n + 1))
      refine PHarmLimit p hp hp2 (Ωn n) (fun i => v (φ (i + (n + 1))))
        (fun i => gg (φ (i + (n + 1)))) P G (fun i => ?_) (fun K hK hKc => ?_) (fun K hK hKc => ?_)
      · exact (PHarmRestrict p hp hp2 (Ωn (φ (i + (n + 1)))) (v (φ (i + (n + 1))))
          (gg (φ (i + (n + 1)))) (hvharm _)).1 _ Metric.isOpen_ball (hsub i)
      · have hKcb : K ⊆ Metric.closedBall (0 : Plane) ((n : ℝ) + 1) :=
          hK.trans Metric.ball_subset_closedBall
        have h1 := hC0 ((n : ℝ) + 1) (hn1 n)
        rw [Metric.tendstoUniformlyOn_iff] at h1 ⊢
        exact fun ε hε => hshift.eventually (h1 ε hε) |>.mono
          fun i hi z hz => hi z (hKcb hz)
      · have hKuniv : K ⊆ (⋃ nn, Ωn nn) := by rw [hunion]; exact Set.subset_univ K
        have h1 := hGconv K hKuniv hKc
        rw [Metric.tendstoUniformlyOn_iff] at h1 ⊢
        intro ε hε
        refine (Filter.tendsto_add_atTop_nat (n + 1)).eventually (h1 ε hε) |>.mono
          fun i hi z hz => ?_
        rw [hgrad (φ (i + (n + 1))) (hsub i (hK hz))]
        exact hi z hz
    have huniv : IsPHarm p Set.univ P G := by
      have h := PHarmUnionExhaustion p hp hp2 Ωn P G hmonoΩ hPharmball
      rwa [hunion] at h
    -- Step 9: Lewis rigidity.
    have hQP : (fun x : Plane => Q (fun _ => x)) = P := by funext x; simp [Q, P]
    have hzero := hL.vanish j hj2 Q G (by rw [hQP]; exact huniv) w
    have hz2 : (1 / (Nat.factorial j : ℝ)) * iteratedFDeriv ℝ j u x₀ (fun _ => w) = 0 := by
      simpa [Q] using hzero
    have hfac : (1 / (Nat.factorial j : ℝ)) ≠ 0 := by
      have := Nat.factorial_pos j
      positivity
    rcases mul_eq_zero.mp hz2 with h | h
    · exact absurd h hfac
    · exact h
  intro j hj2 hjm w
  exact T (m + 1) le_rfl j (by omega) (by omega) w
