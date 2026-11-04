-- Prove2me | solution 1 for ReusablePricing.DPC.step2_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T03:51:21.231345+00:00
-- url     : https://prove2.me/submissions/1419b100-b9af-4dda-bf03-8f2f32f6d64c

import Mathlib
import Definitions.Def_ReusablePricing_DPC_Model
import Definitions.Def_ReusablePricing_DPC_Control
import Theorems.Thm_ReusablePricing_DPC_eq_EC14
import Theorems.Thm_ReusablePricing_DPC_lemma_EC2

open Finset ReusablePricing.DPC

/-- Chain rule for a finite sequence of non-anticipating one-step kernels: the path weights
`∏_t f_t(ω_{<t})(ω_t)` sum to one. -/
lemma dpc_chain_sum_one {α : Type} [Fintype α] [DecidableEq α] [Inhabited α] :
    ∀ (N : ℕ) (f : ℕ → (Fin N → α) → α → ℝ),
      (∀ t ω, ∑ a, f t ω a = 1) →
      (∀ t ω ω', (∀ s : Fin N, s.val < t → ω s = ω' s) → f t ω = f t ω') →
      ∑ ω : Fin N → α, ∏ t : Fin N, f t ω (ω t) = 1 := by
  intro N
  induction N with
  | zero => intro f _ _; simp
  | succ N ih =>
    intro f hsum hdep
    let a0 : α := default
    let g : ℕ → (Fin N → α) → α → ℝ := fun t ω => f t (Fin.snoc ω a0)
    have hg1 : ∀ t ω, ∑ a, g t ω a = 1 := fun t ω => hsum t _
    have hgdep : ∀ t ω ω', (∀ s : Fin N, s.val < t → ω s = ω' s) → g t ω = g t ω' := by
      intro t ω ω' h
      apply hdep
      intro s hs
      cases s using Fin.lastCases with
      | last => simp
      | cast i =>
        simp only [Fin.snoc_castSucc]
        exact h i (by simpa using hs)
    have hsn : ∀ (ω : Fin N → α) (a : α) (t : ℕ), t ≤ N →
        f t (Fin.snoc ω a) = f t (Fin.snoc ω a0) := by
      intro ω a t ht
      apply hdep
      intro s hs
      cases s using Fin.lastCases with
      | last => simp at hs; omega
      | cast i => simp
    have key : ∀ (ω : Fin N → α) (a : α),
        ∏ t : Fin (N + 1), f t (Fin.snoc ω a) ((Fin.snoc ω a : Fin (N+1) → α) t)
          = (∏ t : Fin N, g t ω (ω t)) * f N (Fin.snoc ω a0) a := by
      intro ω a
      rw [Fin.prod_univ_castSucc]
      congr 1
      · apply Finset.prod_congr rfl
        intro t _
        simp only [Fin.snoc_castSucc, Fin.val_castSucc, g]
        rw [hsn ω a t (by omega)]
      · simp only [Fin.snoc_last, Fin.val_last]
        rw [hsn ω a N le_rfl]
    rw [← (Fin.snocEquiv (fun _ => α)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
    rw [← ih g hg1 hgdep]
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    have : ∀ a, (fun x : (fun _ => α) (Fin.last N) × ((i : Fin N) → (fun _ => α) i.castSucc) =>
        ∏ t : Fin (N + 1), f t ((Fin.snocEquiv fun _ => α) x) ((Fin.snocEquiv fun _ => α) x t)) (a, ω)
        = (∏ t : Fin N, g t ω (ω t)) * f N (Fin.snoc ω a0) a := fun a => key ω a
    simp only at this
    rw [Finset.sum_congr rfl (fun a _ => this a), ← Finset.mul_sum, hsum, mul_one]

lemma dpc_q_sum (P : Basic) (x : Fin P.J → ℝ) : ∑ a, P.q x a = 1 := by
  rw [Fintype.sum_option]
  simp [Basic.q]

lemma dpc_outcome_succ (P : Basic) (ω : P.Path) (i : Fin P.T) :
    P.outcome (i.val + 1) ω = ω i := by
  unfold Basic.outcome
  rw [dif_pos ⟨by omega, by omega⟩]
  exact congrArg ω (Fin.ext (by simp))

lemma dpc_D_dep (P : Basic) (ω ω' : P.Path) (t s : ℕ) (hs : s ≤ t)
    (h : ∀ u : Fin P.T, u.val < t → ω u = ω' u) : ∀ j, P.D s ω j = P.D s ω' j := by
  intro j
  unfold Basic.D Basic.outcome
  by_cases hc : 1 ≤ s ∧ s ≤ P.T
  · rw [dif_pos hc, dif_pos hc, h ⟨s - 1, by omega⟩ (by simp; omega)]
  · rw [dif_neg hc, dif_neg hc]

lemma dpc_rate_dep (P : Basic) (ε : ℝ) (nl : ℕ) (t : ℕ) (ω ω' : P.Path)
    (h : ∀ u : Fin P.T, u.val < t → ω u = ω' u) :
    P.dpcRate ε nl (t + 1) ω = P.dpcRate ε nl (t + 1) ω' := by
  have hf : ∀ i, P.freeCap (t + 1) ω i = P.freeCap (t + 1) ω' i := by
    intro i
    unfold Basic.freeCap
    congr 1
    apply Finset.sum_congr rfl
    intro s hs
    rw [Finset.mem_Icc] at hs
    apply Finset.sum_congr rfl
    intro j _
    rw [dpc_D_dep P ω ω' t s (by omega) h j]
  funext j
  unfold Basic.dpcRate
  simp only [hf]

lemma dpc_sum_pathProb (P : Basic) (ε : ℝ) (nl : ℕ) :
    ∑ ω, P.pathProb ε nl ω = 1 := by
  have hprod : ∀ ω, P.pathProb ε nl ω =
      ∏ i : Fin P.T, P.q (P.dpcRate ε nl (i.val + 1) ω) (ω i) := by
    intro ω
    unfold Basic.pathProb
    have hI : Icc 1 P.T = Ico (0 + 1) (P.T + 1) := by ext x; simp only [mem_Icc, mem_Ico]; omega
    rw [hI, ← Finset.prod_Ico_add', ← Finset.range_eq_Ico,
      ← Fin.prod_univ_eq_prod_range (fun i => P.q (P.dpcRate ε nl (i + 1) ω)
        (P.outcome (i + 1) ω))]
    apply Finset.prod_congr rfl
    intro i _
    rw [dpc_outcome_succ]
  simp_rw [hprod]
  exact dpc_chain_sum_one P.T (fun t ω a => P.q (P.dpcRate ε nl (t + 1) ω) a)
    (fun t ω => dpc_q_sum P _)
    (fun t ω ω' h => by simp only [dpc_rate_dep P ε nl t ω ω' h])

lemma dpc_rate_mem (P : Basic) (ε : ℝ) (nl : ℕ) (hU : 0 ≤ P.lamU) (t : ℕ) (ω : P.Path)
    (j : Fin P.J) : 0 ≤ P.dpcRate ε nl t ω j ∧ P.dpcRate ε nl t ω j ≤ P.lamU := by
  unfold Basic.dpcRate
  split_ifs <;> first
    | exact ⟨le_max_left _ _, max_le hU (min_le_left _ _)⟩
    | exact ⟨le_rfl, hU⟩

lemma dpc_pathProb_nonneg (P : Basic) (ε : ℝ) (nl : ℕ) (hU : 0 ≤ P.lamU)
    (hJU : (P.J : ℝ) * P.lamU ≤ 1) (ω : P.Path) : 0 ≤ P.pathProb ε nl ω := by
  unfold Basic.pathProb
  apply Finset.prod_nonneg
  intro t _
  cases h : P.outcome t ω with
  | none =>
    simp only [Basic.q]
    have : ∑ j, P.dpcRate ε nl t ω j ≤ ∑ _j : Fin P.J, P.lamU :=
      Finset.sum_le_sum (fun j _ => (dpc_rate_mem P ε nl hU t ω j).2)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    linarith
  | some j => exact (dpc_rate_mem P ε nl hU t ω j).1

lemma dpc_opnorm_le {J : ℕ} (L : (Fin J → ℝ) →L[ℝ] ℝ) (Ψ : ℝ) (hΨ : 0 ≤ Ψ)
    (h : ∀ j, |L (Pi.single j 1)| ≤ Ψ) : ‖L‖ ≤ Ψ * J := by
  apply ContinuousLinearMap.opNorm_le_bound L (by positivity)
  intro v
  have hv : L v = ∑ i, v i • L (fun j => if i = j then 1 else 0) :=
    LinearMap.pi_apply_eq_sum_univ L.toLinearMap v
  have he : ∀ i : Fin J, (fun j => if i = j then (1 : ℝ) else 0) = Pi.single i 1 := by
    intro i; funext j; simp [Pi.single_apply, eq_comm]
  rw [hv]
  calc ‖∑ i, v i • L (fun j => if i = j then 1 else 0)‖
      ≤ ∑ i, ‖v i • L (fun j => if i = j then 1 else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin J, ‖v‖ * Ψ := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_smul, he i]
        apply mul_le_mul (norm_le_pi_norm v i) _ (norm_nonneg _) (norm_nonneg _)
        rw [Real.norm_eq_abs]; exact h i
    _ = Ψ * J * ‖v‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

lemma dpc_box_convex (P : Basic) (φL φU : ℝ) (t : ℕ) : Convex ℝ (P.Box φL φU t) := by
  intro x hx y hy a b ha hb hab j
  obtain ⟨hx1, hx2⟩ := hx j
  obtain ⟨hy1, hy2⟩ := hy j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have e : P.lamD t j = a * P.lamD t j + b * P.lamD t j := by rw [← add_mul, hab, one_mul]
  have e2 : φL = a * φL + b * φL := by rw [← add_mul, hab, one_mul]
  have e3 : φU = a * φU + b * φU := by rw [← add_mul, hab, one_mul]
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left hx1 ha, mul_le_mul_of_nonneg_left hy1 hb,
    mul_le_mul_of_nonneg_left hx2 ha, mul_le_mul_of_nonneg_left hy2 hb]

/-- First-order revenue loss of shifting the DET rates down by `c = ε/n̲` (A5). -/
lemma dpc_lip (P : Basic) (φL φU Ψ : ℝ) (c : ℝ) (hA5 : P.A5 φL φU Ψ)
    (t : ℕ) (ht : t ∈ Icc 1 P.T) (hc0 : 0 ≤ c) (hcL : c ≤ φL) (hcU : c ≤ φU) :
    P.r t (P.lamD t) - P.r t (fun j => P.lamD t j - c * (if 0 < P.lamD t j then 1 else 0))
      ≤ Ψ * P.J * c := by
  obtain ⟨hφL, hφU, hΨ, hA⟩ := hA5
  have hB := (hA t ht).2
  set y : Fin P.J → ℝ := fun j => P.lamD t j - c * (if 0 < P.lamD t j then 1 else 0) with hy
  have hxs : P.lamD t ∈ P.Box φL φU t := fun j => ⟨by linarith, by linarith⟩
  have hys : y ∈ P.Box φL φU t := by
    intro j
    simp only [hy]
    split_ifs <;> constructor <;> linarith
  have key := Convex.norm_image_sub_le_of_norm_fderiv_le (f := P.r t) (C := Ψ * P.J)
    (fun x hx => (hB x hx).1)
    (fun x hx => dpc_opnorm_le _ Ψ hΨ.le (hB x hx).2.2.1) (dpc_box_convex P φL φU t) hys hxs
  have hn : ‖P.lamD t - y‖ ≤ c := by
    apply (pi_norm_le_iff_of_nonneg hc0).mpr
    intro j
    simp only [hy, Pi.sub_apply, Real.norm_eq_abs]
    split_ifs
    · rw [show P.lamD t j - (P.lamD t j - c * 1) = c by ring, abs_of_nonneg hc0]
    · simp [hc0]
  rw [Real.norm_eq_abs] at key
  have h2 : Ψ * P.J * ‖P.lamD t - y‖ ≤ Ψ * P.J * c :=
    mul_le_mul_of_nonneg_left hn (by positivity)
  linarith [le_abs_self (P.r t (P.lamD t) - P.r t y)]

/-- Under the standing hypotheses, `φ_L + φ_U < 1`. -/
lemma dpc_phi_small' (P : Basic) (φL φU Ψ R : ℝ) (nl : ℕ)
    (hP : P.Standing φL φU Ψ R nl) : φL + φU < 1 := by
  obtain ⟨hMF, -, hW, -, hA5, hNb, -⟩ := hP
  obtain ⟨-, -, hn1, hT1, hdvd, -, -, -, -, hlamU1, -⟩ := hMF
  obtain ⟨-, -, -, hA5t⟩ := hA5
  obtain ⟨-, j, t, ht, hcnt, -⟩ := hNb
  rw [Finset.mem_Icc] at ht
  have hnT : P.n ≤ P.T := Nat.le_of_dvd (by omega) hdvd
  unfold Basic.cnt at hcnt
  obtain ⟨s, hs⟩ := Finset.card_pos.mp hcnt
  rw [Finset.mem_filter, Finset.mem_Icc] at hs
  have hsT : s ∈ Icc 1 P.T := by rw [Finset.mem_Icc]; omega
  rcases hW s hsT j with h0 | ⟨hpos, hlt⟩
  · linarith [hs.2]
  · obtain ⟨h1, h2⟩ := (hA5t s hsT).1 j hpos hlt
    linarith

open scoped Classical in
/-- Per-path bound: `p(ω)(J^D - R(ω)) ≤ p(ω)·TΨJε/n̲ + 1{ω ∉ 𝒢}·p(ω)·2TR`. -/
lemma dpc_pointwise (P : Basic) (φL φU Ψ R : ℝ) (nl : ℕ) (ε δ : ℝ)
    (hP : P.Standing φL φU Ψ R nl)
    (hε0 : 0 ≤ ε) (hε : ε ≤ min φL φU * nl)
    (hδ : δ = ((nl : ℝ) - 1) * (ε - 1) / (3 * nl)) (hnl : (0 : ℝ) < nl) (hR : 0 ≤ R)
    (ω : P.Path) :
    P.pathProb ε nl ω * (P.JD - ∑ t ∈ Icc 1 P.T, P.r t (P.dpcRate ε nl t ω)) ≤
      P.pathProb ε nl ω * (P.T * (Ψ * P.J * (ε / nl))) +
      (if ¬ P.InG ε nl δ ω then P.pathProb ε nl ω else 0) * (2 * P.T * R) := by
  obtain ⟨hMF, hOpt, -, hA4, hA5, -, -⟩ := id hP
  obtain ⟨-, -, -, -, -, -, -, -, hU0, -, hJU⟩ := hMF
  have hp0 := dpc_pathProb_nonneg P ε nl hU0.le hJU ω
  have hJD : P.JD - ∑ t ∈ Icc 1 P.T, P.r t (P.dpcRate ε nl t ω) =
      ∑ t ∈ Icc 1 P.T, (P.r t (P.lamD t) - P.r t (P.dpcRate ε nl t ω)) := by
    unfold Basic.JD Basic.DETObj; rw [Finset.sum_sub_distrib]
  have hcard : ((Icc 1 P.T).card : ℝ) = P.T := by simp
  have hΨ : 0 ≤ Ψ := hA5.2.2.1.le
  have hgen : P.JD - ∑ t ∈ Icc 1 P.T, P.r t (P.dpcRate ε nl t ω) ≤ 2 * P.T * R := by
    rw [hJD]
    calc ∑ t ∈ Icc 1 P.T, (P.r t (P.lamD t) - P.r t (P.dpcRate ε nl t ω))
        ≤ ∑ _t ∈ Icc 1 P.T, 2 * R := by
          apply Finset.sum_le_sum
          intro t ht
          have h1 := (hA4 t ht).2.1 _ (hOpt.1.1 t ht)
          have hm : P.dpcRate ε nl t ω ∈ P.OmegaLam := fun j => dpc_rate_mem P ε nl hU0.le t ω j
          have h2 := (hA4 t ht).2.1 _ hm
          linarith [le_abs_self (P.r t (P.lamD t)), neg_abs_le (P.r t (P.dpcRate ε nl t ω))]
      _ = 2 * P.T * R := by rw [Finset.sum_const, nsmul_eq_mul, hcard]; ring
  have hA : 0 ≤ P.pathProb ε nl ω * (P.T * (Ψ * P.J * (ε / nl))) := by positivity
  by_cases hG : P.InG ε nl δ ω
  · rw [if_neg (not_not.mpr hG), zero_mul, add_zero]
    rcases hp0.lt_or_eq with hpos | hzero
    · apply mul_le_mul_of_nonneg_left _ hp0
      have h14 := eq_EC14 P φL φU Ψ R nl ε δ hP (le_trans hε (le_refl _)) hδ ω hpos hG
      rw [hJD]
      calc ∑ t ∈ Icc 1 P.T, (P.r t (P.lamD t) - P.r t (P.dpcRate ε nl t ω))
          ≤ ∑ _t ∈ Icc 1 P.T, Ψ * P.J * (ε / nl) := by
            apply Finset.sum_le_sum
            intro t ht
            have hrate : P.dpcRate ε nl t ω =
                fun j => P.lamD t j - ε / nl * (if 0 < P.lamD t j then 1 else 0) := by
              funext j; exact h14 t ht j
            rw [hrate]
            have hmin : ε / nl ≤ min φL φU := (div_le_iff₀ hnl).mpr hε
            exact dpc_lip P φL φU Ψ (ε / nl) hA5 t ht (by positivity)
              (le_trans hmin (min_le_left _ _)) (le_trans hmin (min_le_right _ _))
        _ = P.T * (Ψ * P.J * (ε / nl)) := by rw [Finset.sum_const, nsmul_eq_mul, hcard]
    · rw [← hzero]; simp
  · rw [if_pos hG]
    have := mul_le_mul_of_nonneg_left hgen hp0
    nlinarith

open scoped Classical in
theorem solution (P : Basic) (φL φU Ψ R : ℝ) (nl : ℕ) (ε δ : ℝ)
    (hP : P.Standing φL φU Ψ R nl)
    (hε1 : 1 < ε) (hε : ε ≤ min φL φU * nl)
    (hδ : δ = ((nl : ℝ) - 1) * (ε - 1) / (3 * nl))
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) :
    P.JD - P.expRevenue ε nl ≤
      (P.T : ℝ) * (Ψ * P.J * ε / nl +
        4 * R * P.J * P.T / P.n * Real.exp (P.minCapN * γ ^ 2 - δ * γ)) := by
  have hphi := dpc_phi_small' P φL φU Ψ R nl hP
  obtain ⟨hMF, hOpt, -, hA4, hA5, -, -⟩ := id hP
  obtain ⟨-, -, hn1, hT1, -, -, -, -, hU0, -, hJU⟩ := id hMF
  obtain ⟨hφL, hφU, hΨ, -⟩ := id hA5
  have hminpos : 0 < min φL φU := lt_min hφL hφU
  have hnl : (0 : ℝ) < nl := by
    by_contra hc
    push Not at hc
    have : min φL φU * nl ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hminpos.le hc
    linarith
  have hmin : min φL φU < 1 / 2 := by
    rcases le_total φL φU with h | h
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right h]; linarith
  have hnl2 : (2 : ℝ) < nl := by nlinarith
  have hδpos : 0 < δ := by
    rw [hδ]; apply div_pos
    · apply mul_pos <;> linarith
    · linarith
  -- `R ≥ 0`
  have hR : 0 ≤ R := by
    have h1 : (1 : ℕ) ∈ Icc 1 P.T := by rw [Finset.mem_Icc]; omega
    have h0 : (0 : Fin P.J → ℝ) ∈ P.OmegaLam := fun j => ⟨le_rfl, hU0.le⟩
    exact le_trans (abs_nonneg _) ((hA4 1 h1).2.1 0 h0)
  have hEC2 := lemma_EC2 P φL φU Ψ R nl ε δ hP (by linarith) hδpos γ hγ0 hγ1
  have hsum := dpc_sum_pathProb P ε nl
  have hpw := dpc_pointwise P φL φU Ψ R nl ε δ hP (by linarith) hε hδ hnl hR
  have hLHS : P.JD - P.expRevenue ε nl =
      ∑ ω, P.pathProb ε nl ω * (P.JD - ∑ t ∈ Icc 1 P.T, P.r t (P.dpcRate ε nl t ω)) := by
    unfold Basic.expRevenue Basic.E
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul]
  have hprob : P.prob ε nl (fun ω => ¬ P.InG ε nl δ ω) =
      ∑ ω, (if ¬ P.InG ε nl δ ω then P.pathProb ε nl ω else 0) := by
    unfold Basic.prob
    exact Finset.sum_congr rfl (fun ω _ => by congr)
  rw [hLHS]
  calc ∑ ω, P.pathProb ε nl ω * (P.JD - ∑ t ∈ Icc 1 P.T, P.r t (P.dpcRate ε nl t ω))
      ≤ ∑ ω, (P.pathProb ε nl ω * (P.T * (Ψ * P.J * (ε / nl))) +
          (if ¬ P.InG ε nl δ ω then P.pathProb ε nl ω else 0) * (2 * P.T * R)) :=
        Finset.sum_le_sum (fun ω _ => hpw ω)
    _ = P.T * (Ψ * P.J * (ε / nl)) +
          P.prob ε nl (fun ω => ¬ P.InG ε nl δ ω) * (2 * P.T * R) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, hsum, one_mul, hprob]
    _ ≤ P.T * (Ψ * P.J * (ε / nl)) +
          (2 * (P.J : ℝ) * P.T / P.n * Real.exp (P.minCapN * γ ^ 2 - δ * γ)) * (2 * P.T * R) := by
        have : 0 ≤ 2 * (P.T : ℝ) * R := by positivity
        nlinarith [mul_le_mul_of_nonneg_right hEC2 this]
    _ = _ := by ring
