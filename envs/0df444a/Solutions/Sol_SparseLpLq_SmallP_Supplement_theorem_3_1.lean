-- Prove2me | solution 1 for SparseLpLq.SmallP.Supplement.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:39:38.054499+00:00
-- url     : https://prove2.me/submissions/4a2f2f9a-22f8-4e86-af16-257932eb91b3

import Mathlib
import Definitions.Def_SparseLpLq_SmallP_Setting
import Definitions.Def_SparseLpLq_SmallP_Supplement_Variational
import Definitions.Def_SparseLpLq_SmallP_Supplement_SPeL1

open scoped ENNReal Matrix Topology

open SparseLpLq
open SparseLpLq.SmallP
open SparseLpLq.SmallP.Supplement

open SparseLpLq.SmallP
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (σ : ℝ)
    (hσ : 0 ≤ σ) (hfeas : (FEA A b σ 1).Nonempty) (hb : σ < qNorm 1 b)
    (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    (xfeas : Fin n → ℝ) (lam0 μ0 ν0 ε0 ρ θ : ℝ) (hθρ : θ * ρ ≤ 1)
    (x : ℕ → Fin n → ℝ) (hx : IsSPeL1 A b σ p xfeas lam0 μ0 ν0 ε0 ρ θ x) :
    -- (i)
    Bornology.IsBounded (Set.range x) ∧
    -- (ii)
    (∀ xs : Fin n → ℝ, MapClusterPt xs Filter.atTop x → xs ∈ FEA A b σ 1) ∧
    -- (iii)
    (∀ xs : Fin n → ℝ, MapClusterPt xs Filter.atTop x →
      {d | -d ∈ horizonSubdiff (PhiE p) (WithLp.toLp 2 xs)} ∩ normalConeFEA A b σ xs = {0} →
      IsStationary A b σ p xs) := by
        have hp0' : p ≠ 0 := hp.1.ne'
        have hlp' : ∀ y : Fin n → ℝ, lpObj p y = ∑ i, |y i| ^ p := by
          intro y; simp [lpObj, hp0']
        set D : ℝ → ℝ := fun t => 2 * t * (p / 2) * (t ^ 2) ^ (p / 2 - 1) with hD
        have hφeq : ∀ t : ℝ, |t| ^ p = (t ^ 2) ^ (p / 2) := by
          intro t
          rw [← sq_abs t, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
          norm_num
          ring_nf
        have hderiv : ∀ t : ℝ, t ≠ 0 → HasDerivAt (fun s : ℝ => |s| ^ p) (D t) t := by
          intro t ht
          have h1 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
            simpa using hasDerivAt_pow 2 t
          have h2 := h1.rpow_const (p := p / 2) (Or.inl (pow_ne_zero 2 ht))
          have : (fun s : ℝ => |s| ^ p) = fun s => (s ^ 2) ^ (p / 2) := funext hφeq
          rw [this]; exact h2
        have hDcont : ∀ t : ℝ, t ≠ 0 → ContinuousAt D t := by
          intro t ht
          rw [hD]
          apply ContinuousAt.mul (by fun_prop)
          exact ContinuousAt.rpow_const (by fun_prop) (Or.inl (pow_ne_zero 2 ht))
        have hL1 : ∀ a u ε : ℝ, 0 < ε → (a ≠ 0 → u = D a) →
            ∀ᶠ t in 𝓝 a, |a| ^ p + u * (t - a) - ε * |t - a| ≤ |t| ^ p := by
          intro a u ε hε hu
          by_cases ha : a = 0
          · subst ha
            have hc : ContinuousAt (fun t : ℝ => |t| ^ (1 - p)) 0 :=
              (continuous_abs.continuousAt).rpow_const (Or.inr (by linarith [hp.2]))
            have h0 : (fun t : ℝ => |t| ^ (1 - p)) 0 = 0 := by
              simp only [abs_zero]; exact Real.zero_rpow (by linarith [hp.2])
            have hev : ∀ᶠ t in 𝓝 (0:ℝ), |t| ^ (1 - p) < 1 / (|u| + 1) := by
              have hpos : (fun t : ℝ => |t| ^ (1 - p)) 0 < 1 / (|u| + 1) := by
                rw [h0]; positivity
              exact hc.eventually (gt_mem_nhds hpos)
            filter_upwards [hev] with t ht
            simp only [abs_zero, sub_zero, Real.zero_rpow hp0', zero_add]
            have hsplit : |t| = |t| ^ (1 - p) * |t| ^ p := by
              rw [← Real.rpow_add' (abs_nonneg _) (by norm_num), sub_add_cancel, Real.rpow_one]
            have hq : 0 ≤ |t| ^ p := Real.rpow_nonneg (abs_nonneg _) _
            have hr : 0 ≤ |t| ^ (1 - p) := Real.rpow_nonneg (abs_nonneg _) _
            have h3 : |u| * |t| ^ (1 - p) ≤ 1 := by
              rw [lt_div_iff₀ (by positivity)] at ht
              nlinarith [abs_nonneg u]
            have h4 : u * t ≤ |u| * |t| := by
              rw [← abs_mul]; exact le_abs_self _
            have h5 : |u| * |t| ≤ |t| ^ p := by
              have e : |u| * |t| = (|u| * |t| ^ (1 - p)) * |t| ^ p := by rw [mul_assoc, ← hsplit]
              rw [e]; nlinarith
            nlinarith [abs_nonneg t]
          · have hd := hderiv a ha
            rw [hasDerivAt_iff_isLittleO] at hd
            have := hd.def hε
            filter_upwards [this] with t ht
            rw [hu ha]
            simp only [Real.norm_eq_abs, smul_eq_mul] at ht
            have := (abs_le.1 ht).1
            linarith
        have hL2 : ∀ (y ξ : EuclideanSpace ℝ (Fin n)) (i : Fin n),
            ξ ∈ NAPPAL.VPEB.frechetSubdiff (PhiE p) y → y i ≠ 0 → ξ i = D (y i) := by
          intro y ξ i hξ hyi
          obtain ⟨-, hξ⟩ := hξ
          have hkey : ∀ ε : ℝ, 0 < ε → |ξ i - D (y i)| ≤ 2 * ε := by
            intro ε hε
            have hγ : Filter.Tendsto (fun s : ℝ => y + EuclideanSpace.single i s) (𝓝 0) (𝓝 y) := by
              have : Continuous (fun s : ℝ => y + EuclideanSpace.single i s) :=
                continuous_const.add ((PiLp.continuous_toLp 2 _).comp (continuous_single (A := fun _ : Fin n => ℝ) i))
              have h0 := this.tendsto 0
              rwa [show EuclideanSpace.single i (0:ℝ) = 0 by ext j; simp [PiLp.single_apply],
                add_zero] at h0
            have h1 := hγ.eventually (hξ ε hε)
            have hσ : Filter.Tendsto (fun s : ℝ => y i + s) (𝓝 0) (𝓝 (y i)) := by
              simpa using (tendsto_const_nhds (x := y i)).add (Filter.tendsto_id (x := 𝓝 (0:ℝ)))
            have h2 := hσ.eventually ((hasDerivAt_iff_isLittleO.1 (hderiv _ hyi)).def hε)
            have hsum : ∀ s : ℝ, lpObj p (WithLp.ofLp (y + EuclideanSpace.single i s))
                = lpObj p (WithLp.ofLp y) + (|y i + s| ^ p - |y i| ^ p) := by
              intro s
              rw [hlp', hlp', ← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib]
              rw [Finset.sum_eq_single i]
              · simp
              · intro j _ hj
                simp [PiLp.single_apply, hj]
              · simp
            obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (h1.and h2)
            have hs : ∀ s : ℝ, |s| < δ → s * (ξ i - D (y i)) ≤ 2 * ε * |s| := by
              intro s hs
              have := hball (y := s) (by simpa [Real.dist_eq] using hs)
              obtain ⟨ha, hb⟩ := this
              simp only [PhiE, hsum, add_sub_cancel_left, EuclideanSpace.inner_single_right,
                PiLp.norm_single, Real.norm_eq_abs, conj_trivial] at ha
              rw [← EReal.coe_add, EReal.coe_le_coe_iff] at ha
              simp only [Real.norm_eq_abs, add_sub_cancel_left, smul_eq_mul] at hb
              have := (abs_le.1 hb).2
              nlinarith
            have hp1 := hs (δ / 2) (by rw [abs_of_pos (by positivity)]; linarith)
            have hp2 := hs (-(δ / 2)) (by rw [abs_neg, abs_of_pos (by positivity)]; linarith)
            rw [abs_neg, abs_of_pos (by positivity)] at hp2
            rw [abs_of_pos (by positivity)] at hp1
            rw [abs_le]; constructor <;> nlinarith
          by_contra hne
          have hpos : 0 < |ξ i - D (y i)| := abs_pos.2 (sub_ne_zero.2 hne)
          have := hkey (|ξ i - D (y i)| / 4) (by positivity)
          linarith
        have hL3 : ∀ (y ξ : EuclideanSpace ℝ (Fin n)) (i : Fin n),
            ξ ∈ NAPPAL.VPEB.limSubdiff (PhiE p) y → y i ≠ 0 → ξ i = D (y i) := by
          intro y ξ i hξ hyi
          obtain ⟨-, ys, ξs, hys, -, hξs, hlim⟩ := hξ
          have hyc : Filter.Tendsto (fun j => ys j i) Filter.atTop (𝓝 (y i)) :=
            ((PiLp.continuous_apply 2 _ i).tendsto y).comp hys
          have hξc : Filter.Tendsto (fun j => ξs j i) Filter.atTop (𝓝 (ξ i)) :=
            ((PiLp.continuous_apply 2 _ i).tendsto ξ).comp hlim
          have hne : ∀ᶠ j in Filter.atTop, ys j i ≠ 0 := hyc.eventually (isOpen_ne.mem_nhds hyi)
          have hD : Filter.Tendsto (fun j => ξs j i) Filter.atTop (𝓝 (D (y i))) := by
            have : Filter.Tendsto (fun j => D (ys j i)) Filter.atTop (𝓝 (D (y i))) :=
              (hDcont _ hyi).tendsto.comp hyc
            refine this.congr' ?_
            filter_upwards [hne] with j hj
            exact (hL2 _ _ i (hξs j) hj).symm
          exact tendsto_nhds_unique hξc hD
        have hL4 : ∀ (y0 u : EuclideanSpace ℝ (Fin n)), (∀ i, y0 i ≠ 0 → u i = D (y0 i)) →
            ∀ ε : ℝ, 0 < ε → ∀ᶠ y in 𝓝 y0,
              lpObj p (WithLp.ofLp y0) + (inner ℝ u (y - y0) - ε * ‖y - y0‖) ≤ lpObj p (WithLp.ofLp y) := by
          intro y0 u hu ε hε
          have hε' : 0 < ε / (n + 1) := by positivity
          have hall : ∀ᶠ y in 𝓝 y0, ∀ i, |y0 i| ^ p + u i * (y i - y0 i) - ε / (n + 1) * |y i - y0 i|
              ≤ |y i| ^ p := by
            rw [Filter.eventually_all]
            intro i
            exact ((PiLp.continuous_apply 2 _ i).tendsto y0).eventually
              (hL1 (y0 i) (u i) _ hε' (hu i))
          filter_upwards [hall] with y hy
          rw [hlp', hlp']
          have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hy i)
          rw [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hsum
          have hin : inner ℝ u (y - y0) = ∑ i, u i * (y i - y0 i) := by
            simp [PiLp.inner_apply, mul_comm]
          have hnorm : ∑ i, ε / (n + 1) * |y i - y0 i| ≤ ε * ‖y - y0‖ := by
            calc ∑ i, ε / (n + 1) * |y i - y0 i| ≤ ∑ _i : Fin n, ε / (n + 1) * ‖y - y0‖ := by
                  apply Finset.sum_le_sum; intro i _
                  apply mul_le_mul_of_nonneg_left _ hε'.le
                  have := PiLp.norm_apply_le (y - y0) i
                  simpa using this
              _ = n * (ε / (n + 1)) * ‖y - y0‖ := by simp [Finset.sum_const]; ring
              _ ≤ ε * ‖y - y0‖ := by
                  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
                  rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
          linarith
        obtain ⟨hxf, hlam0, hμ0, hν0, hε0, hρ, hθ0, hθ1, hx0, z, w, hk⟩ := hx
        have hp0 : p ≠ 0 := hp.1.ne'
        have hq1 : ∀ v : Fin m → ℝ, qNorm 1 v = ∑ i, |v i| := by
          intro v
          unfold qNorm
          rw [PiLp.norm_eq_of_L1]
          rfl
        have hlp : ∀ y : Fin n → ℝ, lpObj p y = ∑ i, |y i| ^ p := by
          intro y; simp [lpObj, hp0]
        have hlp0 : ∀ y : Fin n → ℝ, 0 ≤ lpObj p y := by
          intro y; rw [hlp]; exact Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (abs_nonneg _) _)
        have hh_ge : ∀ ν t : ℝ, 0 < ν → |t| ≤ hSm ν t := by
          intro ν t hν
          unfold hSm
          split_ifs with h
          · exact le_rfl
          · have : t ^ 2 / ν + ν / 4 - |t| = (|t| - ν / 2) ^ 2 / ν := by
              field_simp; rw [← sq_abs t]; ring
            have : 0 ≤ (|t| - ν / 2) ^ 2 / ν := by positivity
            linarith
        have hh_le : ∀ ν t : ℝ, 0 < ν → hSm ν t ≤ |t| + ν / 4 := by
          intro ν t hν
          unfold hSm
          split_ifs with h
          · linarith
          · push Not at h
            have h1 : t ^ 2 ≤ |t| * ν := by
              rw [← sq_abs t, sq]; exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
            have : t ^ 2 / ν ≤ |t| := by rw [div_le_iff₀ hν]; exact h1
            linarith
        have hg_ge : ∀ μ s : ℝ, 0 < μ → max s 0 ≤ gSm μ s := by
          intro μ s hμ
          unfold gSm
          split_ifs with h
          · exact le_rfl
          · have e1 : s ^ 2 / (2 * μ) + s / 2 + μ / 8 = (s + μ / 2) ^ 2 / (2 * μ) := by
              field_simp; ring
            have e2 : s ^ 2 / (2 * μ) + s / 2 + μ / 8 - s = (s - μ / 2) ^ 2 / (2 * μ) := by
              field_simp; ring
            have : 0 ≤ (s + μ / 2) ^ 2 / (2 * μ) := by positivity
            have : 0 ≤ (s - μ / 2) ^ 2 / (2 * μ) := by positivity
            apply max_le <;> linarith
        have hg_le : ∀ μ s : ℝ, 0 < μ → gSm μ s ≤ max s 0 + μ / 8 := by
          intro μ s hμ
          unfold gSm
          split_ifs with h
          · linarith
          · push Not at h
            rw [abs_lt] at h
            rcases le_or_gt 0 s with hs | hs
            · have : s ^ 2 / (2 * μ) ≤ s / 2 := by
                rw [div_le_iff₀ (by positivity)]; nlinarith
              have : s ≤ max s 0 := le_max_left _ _
              linarith
            · have : s ^ 2 / (2 * μ) + s / 2 ≤ 0 := by
                have : s ^ 2 / (2 * μ) + s / 2 = s * (s + μ) / (2 * μ) := by field_simp
                rw [this]; apply div_nonpos_of_nonpos_of_nonneg _ (by positivity); nlinarith
              have : 0 ≤ max s 0 := le_max_right _ _
              linarith
        have hH_ge : ∀ ν : ℝ, 0 < ν → ∀ v : Fin m → ℝ, qNorm 1 v ≤ HSm ν v := by
          intro ν hν v
          rw [hq1]; unfold HSm
          exact Finset.sum_le_sum (fun i _ => hh_ge ν (v i) hν)
        have hH_le : ∀ ν : ℝ, 0 < ν → ∀ v : Fin m → ℝ, HSm ν v ≤ qNorm 1 v + m * (ν / 4) := by
          intro ν hν v
          rw [hq1]; unfold HSm
          calc ∑ i, hSm ν (v i) ≤ ∑ i, (|v i| + ν / 4) := Finset.sum_le_sum (fun i _ => hh_le ν (v i) hν)
            _ = ∑ i, |v i| + m * (ν / 4) := by simp [Finset.sum_add_distrib]
        set C : ℝ := lpObj p xfeas + lam0 * (m * (ν0 / 4) + μ0 / 8) with hC
        have hρk : ∀ k : ℕ, 0 < ρ ^ k := fun k => pow_pos (by linarith) k
        have hθk : ∀ k : ℕ, 0 < θ ^ k := fun k => pow_pos hθ0 k
        have hρθ : ∀ k : ℕ, ρ ^ k * θ ^ k ≤ 1 := by
          intro k; rw [← mul_pow]; exact pow_le_one₀ (by positivity) (by linarith)
        have hFfeas : ∀ k : ℕ, FSm A b σ p (ρ ^ k * lam0) (θ ^ k * μ0) (θ ^ k * ν0) xfeas ≤ C := by
          intro k
          unfold FSm fSm
          have hν : 0 < θ ^ k * ν0 := mul_pos (hθk k) hν0
          have hμ : 0 < θ ^ k * μ0 := mul_pos (hθk k) hμ0
          have h1 := hH_le _ hν (A *ᵥ xfeas - b)
          have h2 : qNorm 1 (A *ᵥ xfeas - b) ≤ σ := hxf
          have h3 := hg_le _ (HSm (θ ^ k * ν0) (A *ᵥ xfeas - b) - σ) hμ
          have h4 : max (HSm (θ ^ k * ν0) (A *ᵥ xfeas - b) - σ) 0 ≤ m * (θ ^ k * ν0 / 4) := by
            apply max_le
            · linarith
            · positivity
          have h5 : ρ ^ k * lam0 * gSm (θ ^ k * μ0) (HSm (θ ^ k * ν0) (A *ᵥ xfeas - b) - σ)
              ≤ ρ ^ k * lam0 * (θ ^ k * (m * (ν0 / 4) + μ0 / 8)) := by
            apply mul_le_mul_of_nonneg_left _ (by have := hρk k; positivity)
            have : m * (θ ^ k * ν0 / 4) + θ ^ k * μ0 / 8 = θ ^ k * (m * (ν0 / 4) + μ0 / 8) := by ring
            linarith
          have h6 : ρ ^ k * lam0 * (θ ^ k * (m * (ν0 / 4) + μ0 / 8))
              = (ρ ^ k * θ ^ k) * (lam0 * (m * (ν0 / 4) + μ0 / 8)) := by ring
          have h7 : (ρ ^ k * θ ^ k) * (lam0 * (m * (ν0 / 4) + μ0 / 8)) ≤ lam0 * (m * (ν0 / 4) + μ0 / 8) := by
            have : 0 ≤ lam0 * (m * (ν0 / 4) + μ0 / 8) := by positivity
            nlinarith [hρθ k]
          rw [hC]; linarith
        have hstep : ∀ k : ℕ, FSm A b σ p (ρ ^ k * lam0) (θ ^ k * μ0) (θ ^ k * ν0) (x (k + 1)) ≤ C := by
          intro k
          obtain ⟨-, -, h3, h4⟩ := hk k
          rw [h4]
          refine le_trans h3 ?_
          split_ifs with h
          · exact le_trans h (hFfeas k)
          · exact hFfeas k
        have hgk : ∀ k : ℕ, ρ ^ k * lam0 * max (qNorm 1 (A *ᵥ x (k + 1) - b) - σ) 0 ≤ C := by
          intro k
          have h := hstep k
          unfold FSm fSm at h
          have hν : 0 < θ ^ k * ν0 := mul_pos (hθk k) hν0
          have hμ : 0 < θ ^ k * μ0 := mul_pos (hθk k) hμ0
          have h1 := hH_ge _ hν (A *ᵥ x (k + 1) - b)
          have h2 := hg_ge _ (HSm (θ ^ k * ν0) (A *ᵥ x (k + 1) - b) - σ) hμ
          have h3 : max (qNorm 1 (A *ᵥ x (k + 1) - b) - σ) 0
              ≤ max (HSm (θ ^ k * ν0) (A *ᵥ x (k + 1) - b) - σ) 0 := max_le_max (by linarith) le_rfl
          have h4 := hlp0 (x (k + 1))
          have h5 : 0 < ρ ^ k * lam0 := mul_pos (hρk k) hlam0
          nlinarith
        have hlpk : ∀ k : ℕ, lpObj p (x (k + 1)) ≤ C := by
          intro k
          have h := hstep k
          unfold FSm fSm at h
          have hμ : 0 < θ ^ k * μ0 := mul_pos (hθk k) hμ0
          have h2 := hg_ge _ (HSm (θ ^ k * ν0) (A *ᵥ x (k + 1) - b) - σ) hμ
          have h5 : 0 < ρ ^ k * lam0 := mul_pos (hρk k) hlam0
          have h6 : 0 ≤ max (HSm (θ ^ k * ν0) (A *ᵥ x (k + 1) - b) - σ) 0 := le_max_right _ _
          nlinarith
        have hC0 : 0 ≤ C := le_trans (hlp0 _) (hlpk 0)
        have hpart1 : Bornology.IsBounded (Set.range x) := by
          rw [isBounded_iff_forall_norm_le]
          refine ⟨max (C ^ (1 / p)) ‖xfeas‖, ?_⟩
          rintro _ ⟨k, rfl⟩
          cases k with
          | zero => rw [hx0]; exact le_max_right _ _
          | succ k =>
            refine (pi_norm_le_iff_of_nonneg (le_trans (by positivity) (le_max_left _ _))).2 ?_
            intro i
            rw [Real.norm_eq_abs]
            refine le_trans ?_ (le_max_left _ _)
            have hi : |x (k + 1) i| ^ p ≤ C := by
              refine le_trans ?_ (hlpk k)
              rw [hlp]
              exact Finset.single_le_sum (f := fun j => |x (k + 1) j| ^ p)
                (fun j _ => Real.rpow_nonneg (abs_nonneg _) _) (Finset.mem_univ i)
            calc |x (k + 1) i| = (|x (k + 1) i| ^ p) ^ (1 / p) := by
                  rw [one_div, Real.rpow_rpow_inv (abs_nonneg _) hp0]
              _ ≤ C ^ (1 / p) := Real.rpow_le_rpow (Real.rpow_nonneg (abs_nonneg _) _) hi
                  (by have := hp.1; positivity)
        have hcont : Continuous (fun y : Fin n → ℝ => qNorm 1 (A *ᵥ y - b)) := by
          simp only [hq1]
          simp only [Matrix.mulVec, dotProduct, Pi.sub_apply]
          fun_prop
        have hpart2 : ∀ xs : Fin n → ℝ, MapClusterPt xs Filter.atTop x → xs ∈ FEA A b σ 1 := by
          intro xs hcl
          show qNorm 1 (A *ᵥ xs - b) ≤ σ
          by_contra hlt
          push Not at hlt
          set δ := (qNorm 1 (A *ᵥ xs - b) - σ) / 2 with hδ
          have hδ0 : 0 < δ := by rw [hδ]; linarith
          have hnear : ∀ᶠ y in 𝓝 xs, σ + δ < qNorm 1 (A *ᵥ y - b) :=
            (hcont.tendsto xs).eventually (lt_mem_nhds (by rw [hδ]; linarith))
          obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (C / (lam0 * δ)) hρ
          have hev : ∀ᶠ k in Filter.atTop, qNorm 1 (A *ᵥ x k - b) < σ + δ := by
            refine Filter.eventually_atTop.2 ⟨K + 1, fun k hkK => ?_⟩
            obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hkK
            rw [show K + 1 + j = (K + j) + 1 by omega]
            have h1 := hgk (K + j)
            have h2 : ρ ^ K ≤ ρ ^ (K + j) := pow_le_pow_right₀ hρ.le (by omega)
            have h3 : C < ρ ^ (K + j) * lam0 * δ := by
              rw [div_lt_iff₀ (by positivity)] at hK
              have : ρ ^ K * (lam0 * δ) ≤ ρ ^ (K + j) * (lam0 * δ) :=
                mul_le_mul_of_nonneg_right h2 (by positivity)
              linarith [mul_assoc (ρ ^ (K + j)) lam0 δ]
            have h4 : max (qNorm 1 (A *ᵥ x (K + j + 1) - b) - σ) 0 < δ := by
              by_contra h5
              push Not at h5
              have : ρ ^ (K + j) * lam0 * δ ≤ ρ ^ (K + j) * lam0 * max (qNorm 1 (A *ᵥ x (K + j + 1) - b) - σ) 0 :=
                mul_le_mul_of_nonneg_left h5 (by have := hρk (K + j); positivity)
              linarith
            have := le_max_left (qNorm 1 (A *ᵥ x (K + j + 1) - b) - σ) 0
            linarith
          obtain ⟨k, hk1, hk2⟩ := ((hcl.frequently hnear).and_eventually hev).exists
          linarith
        refine ⟨hpart1, hpart2, ?_⟩
        intro xs hcl hCQ
        have hxsF := hpart2 xs hcl
        clear hpart1 hstep hgk hlpk hFfeas hρθ hh_ge hh_le hg_ge hg_le hH_ge hlp0 hfeas hb hθρ hx0 hxf hpart2 hC hφeq hderiv hL1 hL2
        have hNC : ∀ v : Fin n → ℝ, (∀ y ∈ FEA A b σ 1, ∑ i, v i * (y i - xs i) ≤ 0) →
            WithLp.toLp 2 v ∈ normalConeFEA A b σ xs := by
          intro v hv
          refine ⟨by simp [indFEA, hxsF], fun _ => WithLp.toLp 2 xs, fun _ => WithLp.toLp 2 v,
            tendsto_const_nhds, tendsto_const_nhds, fun _ => ?_, tendsto_const_nhds⟩
          refine ⟨by simp [indFEA, hxsF], fun ε hε => Filter.Eventually.of_forall fun y => ?_⟩
          by_cases hy : WithLp.ofLp y ∈ FEA A b σ 1
          · have h1 := hv _ hy
            have hin : inner ℝ (WithLp.toLp 2 v) (y - WithLp.toLp 2 xs) = ∑ i, v i * (y i - xs i) := by
              simp [PiLp.inner_apply, mul_comm]
            have h2 : inner ℝ (WithLp.toLp 2 v) (y - WithLp.toLp 2 xs) - ε * ‖y - WithLp.toLp 2 xs‖ ≤ 0 := by
              rw [hin]; nlinarith [norm_nonneg (y - WithLp.toLp 2 xs)]
            simp only [indFEA, hy, hxsF, if_true, zero_add]
            exact_mod_cast h2
          · simp [indFEA, hy]
        have hHor : ∀ v : Fin n → ℝ, (∀ i, xs i ≠ 0 → v i = 0) →
            -(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n)) ∈ horizonSubdiff (PhiE p) (WithLp.toLp 2 xs) := by
          intro v hv
          set u0 : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => D (xs i)) with hu0
          refine ⟨by simp [PhiE], fun _ => WithLp.toLp 2 xs,
            fun k => u0 + ((k : ℝ) + 1) • (-(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))),
            fun k => 1 / ((k : ℝ) + 1), tendsto_const_nhds, tendsto_const_nhds, fun k => ?_,
            fun k => by positivity, tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
          · refine ⟨by simp [PhiE], fun ε hε => ?_⟩
            have hu : ∀ i, (WithLp.toLp 2 xs : EuclideanSpace ℝ (Fin n)) i ≠ 0 →
                (u0 + ((k : ℝ) + 1) • (-(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n)))) i
                  = D ((WithLp.toLp 2 xs : EuclideanSpace ℝ (Fin n)) i) := by
              intro i hi
              have := hv i hi
              simp [hu0, this]
            filter_upwards [hL4 _ _ hu ε hε] with y hy
            simp only [PhiE]
            rw [← EReal.coe_add]
            exact EReal.coe_le_coe_iff.2 hy
          · have heq : (fun k : ℕ => (1 / ((k : ℝ) + 1)) •
                (u0 + ((k : ℝ) + 1) • (-(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n)))))
                = fun k : ℕ => (1 / ((k : ℝ) + 1)) • u0 + (-(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))) := by
              funext k
              rw [smul_add, smul_smul, one_div, inv_mul_cancel₀ (by positivity), one_smul]
            rw [heq]
            have _inst : ContinuousSMul ℝ (EuclideanSpace ℝ (Fin n)) := inferInstance
            have h1 : Filter.Tendsto (fun k : ℕ => (1 / ((k : ℝ) + 1)) • u0) Filter.atTop
                (𝓝 ((0 : ℝ) • u0)) := tendsto_one_div_add_atTop_nhds_zero_nat.smul_const u0
            rw [zero_smul] at h1
            have := h1.add_const (-(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n)))
            simpa using this
        -- subsequence
        obtain ⟨ψ, hψmono, hψ⟩ := hcl.tendsto_subseq
        set kk : ℕ → ℕ := fun j => ψ (j + 1) - 1 with hkkdef
        have hkk1 : ∀ j, kk j + 1 = ψ (j + 1) := by
          intro j; have : j + 1 ≤ ψ (j + 1) := hψmono.id_le (j + 1); simp only [hkkdef]; omega
        have hkkj : ∀ j, j ≤ kk j := by
          intro j; have : j + 1 ≤ ψ (j + 1) := hψmono.id_le (j + 1); simp only [hkkdef]; omega
        have hkkt : Filter.Tendsto kk Filter.atTop Filter.atTop :=
          Filter.tendsto_atTop_mono hkkj Filter.tendsto_id
        have hZt : Filter.Tendsto (fun j => z (kk j)) Filter.atTop (𝓝 xs) := by
          have h1 := hψ.comp (Filter.tendsto_add_atTop_nat 1)
          refine h1.congr (fun j => ?_)
          simp only [Function.comp]
          rw [← hkk1 j]
          exact (hk (kk j)).2.2.2
        have hθt : Filter.Tendsto (fun j => θ ^ (kk j)) Filter.atTop (𝓝 0) :=
          (tendsto_pow_atTop_nhds_zero_of_lt_one hθ0.le hθ1).comp hkkt
        have hξex : ∀ k, ∃ ξ, ξ ∈ NAPPAL.VPEB.limSubdiff (PhiE p) (WithLp.toLp 2 (w k)) ∧
            ‖ξ + WithLp.toLp 2 (gradFSm A b σ (ρ ^ k * lam0) (θ ^ k * μ0) (θ ^ k * ν0) (z k))‖
              ≤ θ ^ k * ε0 := by
          intro k
          obtain ⟨⟨ξ, h1, h2⟩, -⟩ := hk k
          exact ⟨ξ, h1, h2⟩
        choose ξ hξ1 hξ2 using hξex
        set g : ℕ → Fin n → ℝ := fun k =>
          gradFSm A b σ (ρ ^ k * lam0) (θ ^ k * μ0) (θ ^ k * ν0) (z k) with hgdef
        have hεt : Filter.Tendsto (fun j => θ ^ (kk j) * ε0) Filter.atTop (𝓝 0) := by
          simpa using hθt.mul_const ε0
        have hWt : ∀ i, Filter.Tendsto (fun j => w (kk j) i) Filter.atTop (𝓝 (xs i)) := by
          intro i
          have hz : Filter.Tendsto (fun j => z (kk j) i) Filter.atTop (𝓝 (xs i)) :=
            ((continuous_apply i).tendsto xs).comp hZt
          have hd : Filter.Tendsto (fun j => w (kk j) i - z (kk j) i) Filter.atTop (𝓝 0) := by
            refine squeeze_zero_norm (fun j => ?_) hεt
            have h1 := (hk (kk j)).2.1
            have h2 := PiLp.norm_apply_le (WithLp.toLp 2 (w (kk j) - z (kk j))) i
            simp only [qNorm] at h1
            simp only [PiLp.toLp_apply, Pi.sub_apply] at h2
            linarith
          have := hz.add hd
          simpa using this
        have hS : ∀ i, xs i ≠ 0 →
            Filter.Tendsto (fun j => g (kk j) i) Filter.atTop (𝓝 (-D (xs i))) := by
          intro i hi
          have hne : ∀ᶠ j in Filter.atTop, w (kk j) i ≠ 0 := (hWt i).eventually (isOpen_ne.mem_nhds hi)
          have hξc : Filter.Tendsto (fun j => ξ (kk j) i) Filter.atTop (𝓝 (D (xs i))) := by
            have : Filter.Tendsto (fun j => D (w (kk j) i)) Filter.atTop (𝓝 (D (xs i))) :=
              (hDcont _ hi).tendsto.comp (hWt i)
            refine this.congr' ?_
            filter_upwards [hne] with j hj
            exact (hL3 _ _ i (hξ1 (kk j)) hj).symm
          have hsum : Filter.Tendsto (fun j => ξ (kk j) i + g (kk j) i) Filter.atTop (𝓝 0) := by
            refine squeeze_zero_norm (fun j => ?_) hεt
            have h1 := hξ2 (kk j)
            have h2 := PiLp.norm_apply_le (ξ (kk j) + WithLp.toLp 2 (g (kk j))) i
            simp only [PiLp.add_apply, PiLp.toLp_apply] at h2
            exact le_trans h2 h1
          have := hsum.sub hξc
          simpa using this
        clear hk hξ1 hξ2 hL3 hDcont
        have hgform : ∀ k (y : Fin n → ℝ), ∑ i, g k i * (y i - xs i) =
            (ρ ^ k * lam0 * gSmDeriv (θ ^ k * μ0) (HSm (θ ^ k * ν0) (A *ᵥ z k - b) - σ)) *
            ((fun l => hSmDeriv (θ ^ k * ν0) ((A *ᵥ z k - b) l)) ⬝ᵥ ((A *ᵥ y - b) - (A *ᵥ xs - b))) := by
          intro k y
          have e1 : ∑ i, g k i * (y i - xs i) = g k ⬝ᵥ (y - xs) := by simp [dotProduct]
          rw [e1]
          show gradFSm A b σ (ρ ^ k * lam0) (θ ^ k * μ0) (θ ^ k * ν0) (z k) ⬝ᵥ (y - xs) = _
          unfold gradFSm
          rw [smul_dotProduct, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, smul_eq_mul]
          congr 2
          rw [Matrix.mulVec_sub]; abel
        have hhb : ∀ ν t : ℝ, |hSmDeriv ν t| ≤ 1 := by
          intro ν t; unfold hSmDeriv
          rw [abs_le]; exact ⟨le_min (le_max_right _ _) (by norm_num), min_le_right _ _⟩
        have hgd : ∀ μ s : ℝ, 0 ≤ gSmDeriv μ s := fun μ s => le_min (le_max_right _ _) zero_le_one
        have hdot : ∀ h : Fin m → ℝ, (∀ l, |h l| ≤ 1) → ∀ v : Fin m → ℝ, h ⬝ᵥ v ≤ qNorm 1 v := by
          intro h hh v
          rw [hq1]; unfold dotProduct
          apply Finset.sum_le_sum; intro l _
          calc h l * v l ≤ |h l * v l| := le_abs_self _
            _ = |h l| * |v l| := abs_mul _ _
            _ ≤ 1 * |v l| := mul_le_mul_of_nonneg_right (hh l) (abs_nonneg _)
            _ = |v l| := one_mul _
        have hAcont : Continuous (fun y : Fin n → ℝ => A *ᵥ y - b) := by
          refine continuous_pi fun l => ?_
          simp only [Pi.sub_apply, Matrix.mulVec, dotProduct]
          fun_prop
        have hAZ : Filter.Tendsto (fun j => A *ᵥ z (kk j) - b) Filter.atTop (𝓝 (A *ᵥ xs - b)) :=
          (hAcont.tendsto xs).comp hZt
        have hνt : Filter.Tendsto (fun j => θ ^ (kk j) * ν0) Filter.atTop (𝓝 0) := by
          simpa using hθt.mul_const ν0
        have hμt : Filter.Tendsto (fun j => θ ^ (kk j) * μ0) Filter.atTop (𝓝 0) := by
          simpa using hθt.mul_const μ0
        have hNev : ∀ᶠ j in Filter.atTop, ∀ y ∈ FEA A b σ 1, ∑ i, g (kk j) i * (y i - xs i) ≤ 0 := by
          have hr : qNorm 1 (A *ᵥ xs - b) ≤ σ := hxsF
          rcases hr.lt_or_eq with hlt | heq
          · set δ' := (σ - qNorm 1 (A *ᵥ xs - b)) / 3 with hδ'
            have hδ'0 : 0 < δ' := by rw [hδ']; linarith
            have ev1 : ∀ᶠ j in Filter.atTop, qNorm 1 (A *ᵥ z (kk j) - b) < qNorm 1 (A *ᵥ xs - b) + δ' :=
              ((hcont.tendsto xs).comp hZt).eventually (gt_mem_nhds (by linarith))
            have ev2 : ∀ᶠ j in Filter.atTop, (m : ℝ) * (θ ^ (kk j) * ν0 / 4) < δ' := by
              have : Filter.Tendsto (fun j => (m : ℝ) * (θ ^ (kk j) * ν0 / 4)) Filter.atTop (𝓝 0) := by
                simpa using (hνt.div_const 4).const_mul (m : ℝ)
              exact this.eventually (gt_mem_nhds hδ'0)
            have ev3 : ∀ᶠ j in Filter.atTop, θ ^ (kk j) * μ0 / 2 < δ' := by
              have : Filter.Tendsto (fun j => θ ^ (kk j) * μ0 / 2) Filter.atTop (𝓝 0) := by
                simpa using hμt.div_const 2
              exact this.eventually (gt_mem_nhds hδ'0)
            filter_upwards [ev1, ev2, ev3] with j h1 h2 h3
            intro y _
            rw [hgform]
            have hν : 0 < θ ^ (kk j) * ν0 := mul_pos (hθk _) hν0
            have hμ : 0 < θ ^ (kk j) * μ0 := mul_pos (hθk _) hμ0
            have h4 := hH_le _ hν (A *ᵥ z (kk j) - b)
            have h5 : (HSm (θ ^ (kk j) * ν0) (A *ᵥ z (kk j) - b) - σ) / (θ ^ (kk j) * μ0) + 1 / 2 < 0 := by
              have : (HSm (θ ^ (kk j) * ν0) (A *ᵥ z (kk j) - b) - σ) / (θ ^ (kk j) * μ0) < -(1 / 2) := by
                rw [div_lt_iff₀ hμ]; linarith
              linarith
            have h6 : gSmDeriv (θ ^ (kk j) * μ0) (HSm (θ ^ (kk j) * ν0) (A *ᵥ z (kk j) - b) - σ) = 0 := by
              unfold gSmDeriv; rw [max_eq_right h5.le]; norm_num
            rw [h6]; simp
          · have hhr : ∀ l, ∀ᶠ j in Filter.atTop,
                hSmDeriv (θ ^ (kk j) * ν0) ((A *ᵥ z (kk j) - b) l) * (A *ᵥ xs - b) l
                  = |(A *ᵥ xs - b) l| := by
              intro l
              have hc : Filter.Tendsto (fun j => (A *ᵥ z (kk j) - b) l) Filter.atTop
                  (𝓝 ((A *ᵥ xs - b) l)) := ((continuous_apply l).tendsto _).comp hAZ
              rcases lt_trichotomy ((A *ᵥ xs - b) l) 0 with hneg | hz0 | hpos
              · have e1 := hc.eventually (gt_mem_nhds (show (A *ᵥ xs - b) l < (A *ᵥ xs - b) l / 2 by linarith))
                have e2 := hνt.eventually (gt_mem_nhds (show (0:ℝ) < -(A *ᵥ xs - b) l by linarith))
                filter_upwards [e1, e2] with j h1 h2
                have hν : 0 < θ ^ (kk j) * ν0 := mul_pos (hθk _) hν0
                have h3 : 2 / (θ ^ (kk j) * ν0) * (A *ᵥ z (kk j) - b) l ≤ -1 := by
                  rw [div_mul_eq_mul_div, div_le_iff₀ hν]; linarith
                unfold hSmDeriv
                rw [max_eq_right h3, min_eq_left (by norm_num), abs_of_neg hneg]; ring
              · exact Filter.Eventually.of_forall fun j => by simp [hz0]
              · have e1 := hc.eventually (lt_mem_nhds (show (A *ᵥ xs - b) l / 2 < (A *ᵥ xs - b) l by linarith))
                have e2 := hνt.eventually (gt_mem_nhds hpos)
                filter_upwards [e1, e2] with j h1 h2
                have hν : 0 < θ ^ (kk j) * ν0 := mul_pos (hθk _) hν0
                have h3 : 1 ≤ 2 / (θ ^ (kk j) * ν0) * (A *ᵥ z (kk j) - b) l := by
                  rw [div_mul_eq_mul_div, le_div_iff₀ hν]; linarith
                unfold hSmDeriv
                rw [min_eq_right (le_max_of_le_left h3), abs_of_pos hpos]; ring
            filter_upwards [Filter.eventually_all.2 hhr] with j hj
            intro y hy
            rw [hgform]
            apply mul_nonpos_of_nonneg_of_nonpos
            · exact mul_nonneg (mul_pos (hρk _) hlam0).le (hgd _ _)
            · rw [dotProduct_sub]
              have h1 := hdot (fun l => hSmDeriv (θ ^ (kk j) * ν0) ((A *ᵥ z (kk j) - b) l)) (fun l => hhb _ _) (A *ᵥ y - b)
              have h2 : (fun l => hSmDeriv (θ ^ (kk j) * ν0) ((A *ᵥ z (kk j) - b) l)) ⬝ᵥ (A *ᵥ xs - b)
                  = σ := by
                rw [← heq, hq1]; unfold dotProduct
                exact Finset.sum_congr rfl (fun l _ => hj l)
              have h3 : qNorm 1 (A *ᵥ y - b) ≤ σ := hy
              linarith
        obtain ⟨J0, hJ0⟩ := Filter.eventually_atTop.1 hNev
        set G : ℕ → Fin n → ℝ := fun j => g (kk (j + J0)) with hGdef
        have hGN : ∀ j, ∀ y ∈ FEA A b σ 1, ∑ i, G j i * (y i - xs i) ≤ 0 :=
          fun j => hJ0 (j + J0) (by omega)
        have hGS : ∀ i, xs i ≠ 0 → Filter.Tendsto (fun j => G j i) Filter.atTop (𝓝 (-D (xs i))) :=
          fun i hi => (hS i hi).comp (Filter.tendsto_add_atTop_nat J0)
        have hlimN : ∀ (E : ℕ → Fin n → ℝ) (e : Fin n → ℝ), Filter.Tendsto E Filter.atTop (𝓝 e) →
            (∀ j, ∀ y ∈ FEA A b σ 1, ∑ i, E j i * (y i - xs i) ≤ 0) →
            ∀ y ∈ FEA A b σ 1, ∑ i, e i * (y i - xs i) ≤ 0 := by
          intro E e hE hEN y hy
          have hc : Continuous (fun v : Fin n → ℝ => ∑ i, v i * (y i - xs i)) := by fun_prop
          exact le_of_tendsto' ((hc.tendsto e).comp hE) (fun j => hEN j y hy)
        have hGb : Bornology.IsBounded (Set.range G) := by
          by_contra hunb
          have hM : ∀ M : ℝ, ∃ j, M < ‖G j‖ := by
            intro M
            by_contra hcon
            push Not at hcon
            exact hunb ((isBounded_iff_forall_norm_le).2 ⟨M, by rintro _ ⟨j, rfl⟩; exact hcon j⟩)
          choose φ0 hφ0 using fun j : ℕ => hM ((j : ℝ) + 1)
          have hGpos : ∀ j, 0 < ‖G (φ0 j)‖ := fun j => lt_trans (by positivity) (hφ0 j)
          set E : ℕ → Fin n → ℝ := fun j => ‖G (φ0 j)‖⁻¹ • G (φ0 j) with hEdef
          have hE1 : ∀ j, ‖E j‖ = 1 := by
            intro j; rw [hEdef]; simp only
            rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (hGpos j).ne']
          obtain ⟨e, -, φ1, hφ1, hφ1t⟩ := tendsto_subseq_of_bounded (Metric.isBounded_closedBall (x := (0 : Fin n → ℝ)) (r := 1))
            (x := E) (fun j => by simp [hE1 j])
          have he1 : ‖e‖ = 1 := by
            have := (continuous_norm.tendsto e).comp hφ1t
            exact tendsto_nhds_unique this (by simp [Function.comp_def, hE1])
          have heN : ∀ y ∈ FEA A b σ 1, ∑ i, e i * (y i - xs i) ≤ 0 := by
            refine hlimN _ e hφ1t (fun j y hy => ?_)
            simp only [Function.comp, hEdef, Pi.smul_apply, smul_eq_mul]
            have := hGN (φ0 (φ1 j)) y hy
            have h2 : ∑ i, ‖G (φ0 (φ1 j))‖⁻¹ * G (φ0 (φ1 j)) i * (y i - xs i)
                = ‖G (φ0 (φ1 j))‖⁻¹ * ∑ i, G (φ0 (φ1 j)) i * (y i - xs i) := by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
            rw [h2]
            exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 (norm_nonneg _)) this
          have heS : ∀ i, xs i ≠ 0 → e i = 0 := by
            intro i hi
            obtain ⟨B, hB⟩ := (isBounded_iff_forall_norm_le).1 (Metric.isBounded_range_of_tendsto _ (hGS i hi))
            have hB' : ∀ j, |G j i| ≤ B := fun j => by simpa using hB _ ⟨j, rfl⟩
            have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB' 0)
            have hc : Filter.Tendsto (fun j => (E ∘ φ1) j i) Filter.atTop (𝓝 (e i)) :=
              ((continuous_apply i).tendsto e).comp hφ1t
            have hz : Filter.Tendsto (fun j => (E ∘ φ1) j i) Filter.atTop (𝓝 0) := by
              have hb : Filter.Tendsto (fun j : ℕ => B / ((j : ℝ) + 1)) Filter.atTop (𝓝 0) := by
                have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul B
                rw [mul_zero] at this
                exact this.congr (fun j => by ring)
              refine squeeze_zero_norm (fun j => ?_) hb
              have hj1 : (j : ℝ) + 1 ≤ (φ1 j : ℝ) + 1 := by
                have : j ≤ φ1 j := hφ1.id_le j
                exact_mod_cast (by omega : j + 1 ≤ φ1 j + 1)
              have hj2 := hφ0 (φ1 j)
              rw [Real.norm_eq_abs]
              show |‖G (φ0 (φ1 j))‖⁻¹ * G (φ0 (φ1 j)) i| ≤ B / ((j : ℝ) + 1)
              rw [abs_mul, abs_inv, abs_norm, inv_mul_eq_div, div_le_div_iff₀ (hGpos _) (by positivity)]
              calc |G (φ0 (φ1 j)) i| * ((j : ℝ) + 1) ≤ B * ((j : ℝ) + 1) :=
                    mul_le_mul_of_nonneg_right (hB' _) (by positivity)
                _ ≤ B * ‖G (φ0 (φ1 j))‖ := mul_le_mul_of_nonneg_left (by linarith) hB0
            exact tendsto_nhds_unique hc hz
          have hmem : (WithLp.toLp 2 e : EuclideanSpace ℝ (Fin n)) ∈
              {d | -d ∈ horizonSubdiff (PhiE p) (WithLp.toLp 2 xs)} ∩ normalConeFEA A b σ xs :=
            ⟨hHor e heS, hNC e heN⟩
          rw [hCQ] at hmem
          have : e = 0 := by
            have h0 : (WithLp.toLp 2 e : EuclideanSpace ℝ (Fin n)) = 0 := hmem
            funext i
            have := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v i) h0
            simpa using this
          rw [this, norm_zero] at he1
          exact zero_ne_one he1
        obtain ⟨v, -, φ2, hφ2, hφ2t⟩ := tendsto_subseq_of_bounded hGb (x := G) (fun j => Set.mem_range_self j)
        have hvN := hlimN _ v hφ2t (fun j => hGN (φ2 j))
        have hvS : ∀ i, xs i ≠ 0 → -v i = D (xs i) := by
          intro i hi
          have h1 : Filter.Tendsto (fun j => (G ∘ φ2) j i) Filter.atTop (𝓝 (v i)) :=
            ((continuous_apply i).tendsto v).comp hφ2t
          have h2 := (hGS i hi).comp hφ2.tendsto_atTop
          have := tendsto_nhds_unique h1 h2
          rw [this]; ring
        refine ⟨hxsF, by simp [PhiE, indFEA, hxsF], fun _ => WithLp.toLp 2 xs, fun _ => 0,
          tendsto_const_nhds, tendsto_const_nhds, fun _ => ?_, tendsto_const_nhds⟩
        refine ⟨by simp [PhiE, indFEA, hxsF], fun ε hε => ?_⟩
        have hu : ∀ i, (WithLp.toLp 2 xs : EuclideanSpace ℝ (Fin n)) i ≠ 0 →
            (WithLp.toLp 2 (-v) : EuclideanSpace ℝ (Fin n)) i
              = D ((WithLp.toLp 2 xs : EuclideanSpace ℝ (Fin n)) i) := by
          intro i hi
          simpa using hvS i hi
        filter_upwards [hL4 _ _ hu ε hε] with y hy
        by_cases hyF : WithLp.ofLp y ∈ FEA A b σ 1
        · have h1 := hvN _ hyF
          have hin : inner ℝ (WithLp.toLp 2 (-v) : EuclideanSpace ℝ (Fin n)) (y - WithLp.toLp 2 xs)
              = -∑ i, v i * (y i - xs i) := by
            simp [PiLp.inner_apply, mul_comm, Finset.sum_neg_distrib]
          rw [hin] at hy
          have h2 : lpObj p xs + (0 - ε * ‖y - WithLp.toLp 2 xs‖) ≤ lpObj p (WithLp.ofLp y) := by
            simp only at hy; linarith
          simp only [PhiE, indFEA, hyF, hxsF, if_true, add_zero, inner_zero_left]
          rw [← EReal.coe_add]
          exact EReal.coe_le_coe_iff.2 h2
        · simp [PhiE, indFEA, hyF]
