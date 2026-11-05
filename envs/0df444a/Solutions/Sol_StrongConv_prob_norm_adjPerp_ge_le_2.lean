-- Prove2me | solution 2 for StrongConv.prob_norm_adjPerp_ge_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T01:13:39.680386+00:00
-- url     : https://prove2.me/submissions/d0121c2f-6dc4-44e7-89f8-aee8c50b4f21

import Mathlib
import Definitions.Def_StrongConv
import Theorems.Thm_StrongConv_exists_csDistribution_abs_expTr_adjPerp_sub_le
import Theorems.Thm_StrongConv_supp_subset_Icc_of_extends_nuAdj_one
import Theorems.Thm_StrongConv_exists_testFunction
import Theorems.Thm_StrongConv_norm_adjFree

open Polynomial Filter Topology

noncomputable section

namespace StrongConv.T34P

open StrongConv
open scoped Manifold

theorem supp_iteratedDeriv_zero_of_eventually (g : ℝ → ℝ) (x : ℝ) (j : ℕ)
    (h : g =ᶠ[𝓝 x] fun _ => 0) : iteratedDeriv j g x = 0 := by
  rw [h.iteratedDeriv_eq]
  cases j with
  | zero => simp
  | succ n => simp [iteratedDeriv_succ]

/-- A compactly supported distribution whose support lies in `[-ρ, ρ]` kills every smooth function
vanishing on `(-(ρ+δ), ρ+δ)`. -/
theorem eq_zero_of_supp_subset (μ : smoothFun →ₗ[ℝ] ℝ) (hμ : IsCSDistribution μ) (ρ δ : ℝ)
    (hδ : 0 < δ) (hsupp : supp μ ⊆ Set.Icc (-ρ) ρ) (f : smoothFun)
    (hf : ∀ x, |x| < ρ + δ → (f : ℝ → ℝ) x = 0) : μ f = 0 := by
  obtain ⟨c, K, m, hc, hK, hbound⟩ := hμ
  set T : Set ℝ := Set.Icc (-(K+1)) (K+1) \ {x | |x| < ρ + δ} with hT
  have hTc : IsCompact T := isCompact_Icc.diff (isOpen_lt (continuous_abs) continuous_const)
  have hex : ∀ x ∈ T, ∃ A : Set ℝ, IsClosed A ∧ VanishesNear μ A ∧ x ∉ A := by
    intro x hx
    have hx2 : ¬ |x| < ρ + δ := hx.2
    have hxs : x ∉ supp μ := by
      intro h
      have := hsupp h
      rw [Set.mem_Icc] at this
      apply hx2
      rw [abs_lt]; constructor <;> linarith [this.1, this.2]
    simp only [supp, Set.mem_sInter, Set.mem_setOf_eq, not_forall] at hxs
    obtain ⟨A, ⟨h1, h2⟩, h3⟩ := hxs
    exact ⟨A, h1, h2, h3⟩
  choose! A hA using hex
  have hcov : T ⊆ ⋃ x ∈ T, (A x)ᶜ := by
    intro x hx
    simp only [Set.mem_iUnion]
    exact ⟨x, hx, (hA x hx).2.2⟩
  obtain ⟨t, htT, htcov⟩ := hTc.elim_nhds_subcover (fun x => (A x)ᶜ) (fun x hx =>
    ((hA x hx).1.isOpen_compl.mem_nhds (hA x hx).2.2))
  obtain ⟨ψ, hψ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (I := 𝓘(ℝ, ℝ)) (M := ℝ)
    (ι := t) (s := T) (hTc.isClosed) (fun i => (A i)ᶜ)
    (fun i => (hA i (htT i i.2)).1.isOpen_compl) (by
      intro x hx
      have := htcov hx
      simp only [Set.mem_iUnion] at this ⊢
      obtain ⟨i, hi, hxi⟩ := this
      exact ⟨⟨i, hi⟩, hxi⟩)
  have hψs : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (ψ i) := fun i => by
    have := (ψ i).contMDiff
    rw [contMDiff_iff_contDiff] at this
    exact this
  have hfs : ContDiff ℝ (⊤ : ℕ∞) (f : ℝ → ℝ) := f.2
  let P : t → smoothFun := fun i => ⟨fun x => (f : ℝ → ℝ) x * ψ i x, hfs.mul (hψs i)⟩
  have hP : ∀ i, μ (P i) = 0 := by
    intro i
    have hAi := hA i (htT i i.2)
    apply hAi.2.1
    have hopen : IsOpen (tsupport (ψ i))ᶜ := (isClosed_tsupport _).isOpen_compl
    have hsub : A i ⊆ (tsupport (ψ i))ᶜ := by
      intro y hy hy2
      exact (hψ i hy2) hy
    filter_upwards [hopen.mem_nhdsSet.mpr hsub] with y hy
    have : ψ i y = 0 := image_eq_zero_of_notMem_tsupport hy
    show (f : ℝ → ℝ) y * ψ i y = 0
    rw [this, mul_zero]
  let sPsi : ℝ → ℝ := fun x => ∑ i : t, ψ i x
  have hsPsi : ContDiff ℝ (⊤ : ℕ∞) sPsi := by
    apply ContDiff.sum
    intro i _; exact hψs i
  let G : smoothFun := ⟨fun x => (f : ℝ → ℝ) x * (1 - sPsi x), hfs.mul (contDiff_const.sub hsPsi)⟩
  have hdecomp : f = G + ∑ i : t, P i := by
    ext x
    simp [G, P, sPsi, Finset.mul_sum, mul_sub]
  have hG : μ G = 0 := by
    have hzero : ∀ y ∈ Set.Ioo (-(K+1)) (K+1), (G : ℝ → ℝ) y = 0 := by
      intro y hy
      by_cases h : |y| < ρ + δ
      · show (f : ℝ → ℝ) y * (1 - sPsi y) = 0
        rw [hf y h, zero_mul]
      · have hyT : y ∈ T := ⟨⟨hy.1.le, hy.2.le⟩, h⟩
        have := ψ.sum_eq_one hyT
        rw [finsum_eq_sum_of_fintype] at this
        show (f : ℝ → ℝ) y * (1 - sPsi y) = 0
        simp only [sPsi]
        rw [this]; simp
    have hnorm : cNorm m G (-K) K = 0 := by
      unfold cNorm supOn
      apply Finset.sum_eq_zero
      intro j _
      have : (fun x => |iteratedDeriv j (G : ℝ → ℝ) x|) '' Set.Icc (-K) K ⊆ {0} := by
        rintro _ ⟨x, hx, rfl⟩
        have hxI : x ∈ Set.Ioo (-(K+1)) (K+1) := ⟨by linarith [hx.1], by linarith [hx.2]⟩
        have hev : (G : ℝ → ℝ) =ᶠ[𝓝 x] fun _ => 0 := by
          filter_upwards [isOpen_Ioo.mem_nhds hxI] with y hy using hzero y hy
        simp [supp_iteratedDeriv_zero_of_eventually _ x j hev]
      rcases Set.subset_singleton_iff_eq.mp this with h | h
      · rw [h]; simp
      · rw [h]; simp
    have := hbound G
    rw [hnorm, mul_zero] at this
    exact abs_nonpos_iff.mp this
  rw [hdecomp, map_add, hG, map_sum]
  simp [hP]


theorem fnCalc_eq_zero {A : Type*} [CStarAlgebra A] (X : A) (hX : IsSelfAdjoint X) (r : ℝ)
    (hr : ‖X‖ ≤ r) (χ : ℝ → ℝ) (h : ∀ x, |x| ≤ r → χ x = 0) : fnCalc χ X = 0 := by
  by_cases hs : Subsingleton A
  · exact Subsingleton.elim _ _
  haveI : Nontrivial A := not_subsingleton_iff_nontrivial.mp hs
  unfold fnCalc
  rw [← cfc_zero (R := ℂ) X]
  apply cfc_congr
  intro z hz
  have hre := hX.mem_spectrum_eq_re hz
  have hn : ‖z‖ ≤ ‖X‖ := spectrum.norm_le_norm_of_mem hz
  have : |z.re| ≤ r := by
    calc |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
      _ ≤ r := hn.trans hr
  simp [h _ this]

section Part2
open scoped ComplexOrder

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

theorem tr_pos (Y : V →L[ℂ] V) (hY : IsSelfAdjoint Y) (χ : ℝ → ℝ) (h0 : ∀ x, 0 ≤ χ x) :
    0 ≤ fnCalc χ Y := by
  unfold fnCalc
  exact cfc_nonneg (fun x _ => Complex.zero_le_real.mpr (h0 _))

theorem tr_trace_re_nonneg (T : V →L[ℂ] V) (hT : 0 ≤ T) :
    0 ≤ (LinearMap.trace ℂ V (T : V →ₗ[ℂ] V)).re := by
  have hp : (T : V →ₗ[ℂ] V).IsPositive :=
    (ContinuousLinearMap.isPositive_toLinearMap_iff T).mpr
      ((ContinuousLinearMap.nonneg_iff_isPositive T).mp hT)
  exact (Complex.nonneg_iff.mp hp.trace_nonneg).1

theorem tr_trace_re_ge_one (Y : V →L[ℂ] V) (hY : IsSelfAdjoint Y) (χ : ℝ → ℝ)
    (hχc : Continuous χ) (h0 : ∀ x, 0 ≤ χ x) (c : ℝ) (hc : 0 < c)
    (h1 : ∀ x, c ≤ |x| → χ x = 1) (hcY : c ≤ ‖Y‖) :
    1 ≤ (LinearMap.trace ℂ V ((fnCalc χ Y : V →L[ℂ] V) : V →ₗ[ℂ] V)).re := by
  have hnt : Nontrivial V := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have : Y = 0 := Subsingleton.elim _ _
    rw [this, norm_zero] at hcY
    linarith
  obtain ⟨l, hl, hn⟩ := spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty
    (spectrum.nonempty Y)
  rw [hY.spectralRadius_eq_nnnorm] at hn
  have hnorm : ‖l‖ = ‖Y‖ := by
    have := congrArg ENNReal.toReal hn
    simpa using this
  have hre : (l.re : ℂ) = l := (hY.mem_spectrum_eq_re hl).symm
  have habs : c ≤ |l.re| := by
    have h2 : ‖l‖ = |l.re| := by
      conv_lhs => rw [← hre]
      exact Complex.norm_real _
    linarith
  set T := fnCalc χ Y with hTdef
  have hT0 : 0 ≤ T := tr_pos Y hY χ h0
  have hmem : (1 : ℂ) ∈ spectrum ℂ T := by
    have hcont : ContinuousOn (fun z : ℂ => ((χ z.re : ℝ) : ℂ)) (spectrum ℂ Y) := by
      fun_prop
    rw [hTdef, fnCalc, cfc_map_spectrum (hf := hcont) _ Y]
    exact ⟨l, hl, by simp [h1 _ habs]⟩
  have hp : (T : V →ₗ[ℂ] V).IsPositive :=
    (ContinuousLinearMap.isPositive_toLinearMap_iff T).mpr
      ((ContinuousLinearMap.nonneg_iff_isPositive T).mp hT0)
  rw [ContinuousLinearMap.spectrum_eq, ← Module.End.hasEigenvalue_iff_mem_spectrum] at hmem
  obtain ⟨i, hi⟩ := hp.isSymmetric.exists_eigenvalues_eq rfl hmem
  rw [← RCLike.re_to_complex, hp.isSymmetric.re_trace_eq_sum_eigenvalues rfl]
  calc (1:ℝ) = hp.isSymmetric.eigenvalues rfl i := (Complex.ofReal_eq_one.mp hi).symm
    _ ≤ _ := Finset.single_le_sum (fun j _ => hp.nonneg_eigenvalues rfl j) (Finset.mem_univ i)

end Part2

lemma isSA_adj {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {d : ℕ}
    (u : Fin d → H →L[ℂ] H) : IsSelfAdjoint (∑ i, (u i + star (u i))) := by
  unfold IsSelfAdjoint
  rw [star_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [star_add, star_star, add_comm]

lemma isSA_adjPerp {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) : IsSelfAdjoint (adjPerp σ) :=
  isSA_adj (sModel σ)

lemma isSA_adjFree (d : ℕ) : IsSelfAdjoint (adjFree d) :=
  isSA_adj (sLimit d)

/-- An expansion `F N = a + b/N + O(1/N²)` determines the first two asymptotic coefficients. -/
theorem asympCoeff_zero_one (F : ℕ → ℝ) (a b B : ℝ)
    (h : ∀ N : ℕ, 1 ≤ N → |F N - a - b / N| ≤ B / (N : ℝ) ^ 2) :
    asympCoeff F 0 = a ∧ asympCoeff F 1 = b := by
  have hB : ∀ N : ℕ, 1 ≤ N → B / (N : ℝ) ^ 2 ≤ |B| / N := by
    intro N hN
    have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : B * N ≤ |B| * N := mul_le_mul_of_nonneg_right (le_abs_self B) (by positivity)
    have h2 : |B| * N ≤ |B| * (N : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left (by nlinarith) (abs_nonneg B)
    linarith
  have hz : Tendsto (fun N : ℕ => |B| / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have h1 : Tendsto (fun N : ℕ => F N - a - b / N) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hz
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [Real.norm_eq_abs]
    exact (h N hN).trans (hB N hN)
  have hlim : Tendsto F atTop (𝓝 a) := by
    have := (h1.add (tendsto_const_div_atTop_nhds_zero_nat b)).add_const a
    simp only [zero_add] at this
    refine this.congr (fun N => ?_)
    ring
  have hc0 : asympCoeff F 0 = a := by
    rw [asympCoeff]
    have : (fun N : ℕ => (N : ℝ) ^ 0 * (F N - ∑ i : Fin 0, asympCoeff F i / (N : ℝ) ^ (i : ℕ))) = F := by
      funext N; simp
    rw [this]
    exact hlim.limUnder_eq
  refine ⟨hc0, ?_⟩
  have hlim1 : Tendsto (fun N : ℕ => (N : ℝ) ^ 1 * (F N - a)) atTop (𝓝 b) := by
    have h2 : Tendsto (fun N : ℕ => (N : ℝ) ^ 1 * (F N - a) - b) atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ hz
      filter_upwards [eventually_ge_atTop 1] with N hN
      have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
      have e : (N : ℝ) ^ 1 * (F N - a) - b = N * (F N - a - b / N) := by
        field_simp
      rw [Real.norm_eq_abs, e, abs_mul, abs_of_pos hNpos]
      calc (N : ℝ) * |F N - a - b / N| ≤ N * (B / (N : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left (h N hN) hNpos.le
        _ = B / N := by field_simp
        _ ≤ |B| / N := by gcongr; exact le_abs_self B
    have := h2.add_const b
    simp only [zero_add, sub_add_cancel] at this
    exact this
  rw [asympCoeff]
  simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Finset.sum_singleton,
    Fin.val_zero, pow_zero, div_one]
  rw [hc0]
  exact hlim1.limUnder_eq

/-- Markov: `P[‖Aᴺ‖ ≥ c] ≤ N E[tr_N χ(Aᴺ)]` when `χ ≥ 0` and `χ = 1` on `{|x| ≥ c}`. -/
theorem prob_le_mul_expTr_adj (d N : ℕ) (hN : 1 ≤ N) (χ : ℝ → ℝ) (hχc : Continuous χ)
    (h0 : ∀ x, 0 ≤ χ x) (c : ℝ) (hc : 0 < c) (h1 : ∀ x, c ≤ |x| → χ x = 1) :
    uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) => c ≤ ‖adjPerp σ‖) ≤
      (N : ℝ) * uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
        trN N (fnCalc χ (adjPerp σ))) := by
  classical
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  set T : (Fin d → Equiv.Perm (Fin N)) → ℝ := fun σ =>
    (LinearMap.trace ℂ _ ((fnCalc χ (adjPerp σ) : OnesPerp N →L[ℂ] OnesPerp N) :
      OnesPerp N →ₗ[ℂ] OnesPerp N)).re with hT
  have hcard : (0 : ℝ) < Fintype.card (Fin d → Equiv.Perm (Fin N)) := by
    exact_mod_cast Fintype.card_pos
  have hexp : (N : ℝ) * uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
      trN N (fnCalc χ (adjPerp σ))) = (∑ σ, T σ) / Fintype.card (Fin d → Equiv.Perm (Fin N)) := by
    unfold uniformExp trN
    rw [mul_div_assoc', Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [hT]
    field_simp
  rw [hexp]
  unfold uniformProb
  rw [div_le_div_iff_of_pos_right hcard]
  calc ((Finset.univ.filter fun σ : Fin d → Equiv.Perm (Fin N) => c ≤ ‖adjPerp σ‖).card : ℝ)
      = ∑ σ ∈ Finset.univ.filter (fun σ : Fin d → Equiv.Perm (Fin N) => c ≤ ‖adjPerp σ‖),
          (1 : ℝ) := by simp
    _ ≤ ∑ σ ∈ Finset.univ.filter (fun σ : Fin d → Equiv.Perm (Fin N) => c ≤ ‖adjPerp σ‖), T σ := by
        apply Finset.sum_le_sum
        intro σ hσ
        exact tr_trace_re_ge_one _ (isSA_adjPerp σ) χ hχc h0 c hc h1 (Finset.mem_filter.mp hσ).2
    _ ≤ ∑ σ, T σ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro σ _ _
        exact tr_trace_re_nonneg _ (tr_pos _ (isSA_adjPerp σ) χ h0)

/-- The real-number bookkeeping of the proof of Theorem 3.4, with `r = 2d/ε`. -/
theorem arith34 (C8 C4 Nr lg r : ℝ) (hN : 1 ≤ Nr) (hlg : Real.log 2 ≤ lg) (hr : 1 < r) :
    Nr * (|C8| * (1 + lg) ^ 8 / Nr ^ 2 * (1 + Real.log r) *
        ((C4 * 8) ^ 8 * r ^ ((8 : ℝ) + 1 / (1 + Real.log r)))) ≤
      (|C8| * (1 + 1 / Real.log 2) ^ 8 * (C4 * 8) ^ 8 * 2 ^ 8 * Real.exp 1) * (1 / Nr) *
        (r * lg / 2) ^ 8 * (1 + Real.log r) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlg0 : 0 < lg := hl2.trans_le hlg
  have hr0 : 0 < r := by linarith
  have hlogr : 0 < Real.log r := Real.log_pos hr
  have e1 : r ^ ((8 : ℝ) + 1 / (1 + Real.log r)) ≤ r ^ 8 * Real.exp 1 := by
    rw [Real.rpow_add hr0]
    have : r ^ (1 / (1 + Real.log r)) ≤ Real.exp 1 := by
      rw [Real.rpow_def_of_pos hr0]
      apply Real.exp_le_exp.mpr
      rw [mul_one_div, div_le_one (by linarith)]
      linarith
    have h8 : r ^ (8 : ℝ) = r ^ (8 : ℕ) := by norm_cast
    rw [h8]
    gcongr
  have e3 : 1 + lg ≤ (1 + 1 / Real.log 2) * lg := by
    have : 1 ≤ lg / Real.log 2 := by rw [le_div_iff₀ hl2]; linarith
    calc 1 + lg ≤ lg / Real.log 2 + lg := by linarith
      _ = (1 + 1 / Real.log 2) * lg := by field_simp; ring
  have e3' : (1 + lg) ^ 8 ≤ ((1 + 1 / Real.log 2) * lg) ^ 8 :=
    pow_le_pow_left₀ (by linarith) e3 8
  have hN0 : 0 < Nr := by linarith
  have hC4 : 0 ≤ (C4 * 8) ^ 8 := by positivity
  calc Nr * (|C8| * (1 + lg) ^ 8 / Nr ^ 2 * (1 + Real.log r) *
        ((C4 * 8) ^ 8 * r ^ ((8 : ℝ) + 1 / (1 + Real.log r))))
      ≤ Nr * (|C8| * ((1 + 1 / Real.log 2) * lg) ^ 8 / Nr ^ 2 * (1 + Real.log r) *
          ((C4 * 8) ^ 8 * (r ^ 8 * Real.exp 1))) := by
        gcongr
    _ = _ := by field_simp

end StrongConv.T34P

namespace StrongConv

open T34P in
theorem prob_norm_adjPerp_ge_le_dev :
    ∃ C : ℝ, ∀ d N : ℕ, 2 ≤ d → 1 ≤ N → ∀ ε : ℝ, 0 < ε →
      ε < 2 * d - 2 * Real.sqrt (2 * d - 1) →
      uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) =>
          2 * Real.sqrt (2 * d - 1) + ε ≤ ‖adjPerp σ‖) ≤
        C * (1 / N) * (d * Real.log d / ε) ^ 8 * Real.log (2 * Real.exp 1 * d / ε) := by
  obtain ⟨C8, h8⟩ := exists_csDistribution_abs_expTr_adjPerp_sub_le
  obtain ⟨C4, h4⟩ := exists_testFunction
  refine ⟨|C8| * (1 + 1 / Real.log 2) ^ 8 * (C4 * 8) ^ 8 * 2 ^ 8 * Real.exp 1, ?_⟩
  intro d N hd hN ε hε hεK
  obtain ⟨ν, hν, hb⟩ := h8 d
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hK : ‖adjFree d‖ = 2 * Real.sqrt (2 * d - 1) := norm_adjFree d (by omega)
  generalize hρ : 2 * Real.sqrt (2 * d - 1) = ρ at hK hεK ⊢
  have hρpos : 0 < ρ := by
    rw [← hρ]; have : 0 < Real.sqrt (2 * d - 1) := Real.sqrt_pos.mpr (by linarith)
    linarith
  obtain ⟨χ, hχs, hχ01, hχ0, hχ1, hχn⟩ := h4 8 (2 * d) ρ ε (by norm_num) (by positivity) hρpos hε
    (by linarith)
  have hχc : Continuous χ := hχs.continuous
  have h0 : ∀ x, 0 ≤ χ x := fun x => (hχ01 x).1
  let hs : smoothFun := ⟨χ, hχs⟩
  have hcoe : (hs : ℝ → ℝ) = χ := rfl
  -- the distribution of Lemma 8.1 agrees with `ν₁` on polynomials
  have hext : ∀ h : ℝ[X], ν (polyFun h) = nuAdj d 1 h := by
    intro h
    have key := asympCoeff_zero_one (fun N : ℕ => uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
        trN N (fnCalc (fun x => h.eval x) (adjPerp σ))))
      (tau (fnCalc (fun x => h.eval x) (adjFree d))).re (ν (polyFun h))
      (C8 * (1 + Real.log d) ^ 8 * conjExp 2 *
        lpNormCircle 2 (iteratedDeriv 9 (fun θ => h.eval (2 * d * Real.cos θ)))) (fun M hM => by
        have := hb M hM 2 (by norm_num) (polyFun h)
        refine this.trans (le_of_eq ?_)
        change C8 * (1 + Real.log d) ^ 8 / (M : ℝ) ^ 2 * conjExp 2 *
          lpNormCircle 2 (iteratedDeriv 9 (fun θ => h.eval (2 * d * Real.cos θ))) = _
        ring)
    exact key.2.symm
  have hsupp := supp_subset_Icc_of_extends_nuAdj_one d ν hν hext
  rw [hK] at hsupp
  have hν1 : ν hs = 0 :=
    eq_zero_of_supp_subset ν hν ρ (ε / 2) (by positivity) hsupp hs
      (fun x hx => hχ0 x (le_of_lt hx))
  have hτ : fnCalc χ (adjFree d) = 0 :=
    fnCalc_eq_zero _ (isSA_adjFree d) ρ hK.le χ (fun x hx => hχ0 x (by linarith))
  -- the choice `β* = 1 + log(2d/ε)`
  have hr1 : 1 < 2 * d / ε := by rw [lt_div_iff₀ hε]; linarith
  have hLpos : 0 < Real.log (2 * d / ε) := Real.log_pos hr1
  generalize hL : Real.log (2 * d / ε) = L at hLpos
  set β : ℝ := (1 + L) / L with hβ
  have hβ1 : 1 < β := by rw [hβ, lt_div_iff₀ hLpos]; linarith
  have hconj : conjExp β = 1 + L := by
    unfold conjExp; rw [hβ]; field_simp; ring
  have hlp := hχn β hβ1
  rw [hconj] at hlp
  simp only [Nat.cast_ofNat] at hlp
  have hbd := hb N hN β hβ1 hs
  rw [hcoe, hτ, hν1, hconj] at hbd
  have htau0 : (tau (0 : L2Free d →L[ℂ] L2Free d)).re = 0 := by simp [tau]
  rw [htau0, zero_div, sub_zero, sub_zero] at hbd
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hlg0 : 0 ≤ Real.log d := Real.log_nonneg (by linarith)
  have hkey : uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) => trN N (fnCalc χ (adjPerp σ))) ≤
      |C8| * (1 + Real.log d) ^ 8 / (N : ℝ) ^ 2 * (1 + L) *
        ((C4 * 8) ^ 8 * (2 * d / ε) ^ ((8 : ℝ) + 1 / (1 + L))) := by
    refine (le_abs_self _).trans (hbd.trans ?_)
    calc C8 * (1 + Real.log d) ^ 8 / (N : ℝ) ^ 2 * (1 + L) *
          lpNormCircle β (iteratedDeriv 9 (fun θ => χ (2 * d * Real.cos θ)))
        ≤ |C8| * (1 + Real.log d) ^ 8 / (N : ℝ) ^ 2 * (1 + L) *
          lpNormCircle β (iteratedDeriv 9 (fun θ => χ (2 * d * Real.cos θ))) := by
          gcongr
          · exact ENNReal.toReal_nonneg
          · exact le_abs_self _
      _ ≤ _ := by
          gcongr
  have hprob := prob_le_mul_expTr_adj d N hN χ hχc h0 (ρ + ε) (by linarith)
    (fun x hx => hχ1 x hx)
  refine hprob.trans ?_
  have hlg : Real.log 2 ≤ Real.log d := Real.log_le_log (by norm_num) hd'
  have hfa := arith34 C8 C4 (N : ℝ) (Real.log d) (2 * d / ε) (by exact_mod_cast hN) hlg hr1
  rw [hL] at hfa
  have e1 : (2 * d / ε * Real.log d / 2) = d * Real.log d / ε := by field_simp
  have e2 : Real.log (2 * Real.exp 1 * d / ε) = 1 + L := by
    rw [← hL, show 2 * Real.exp 1 * d / ε = Real.exp 1 * (2 * d / ε) by ring,
      Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp]
  rw [e1] at hfa
  rw [e2]
  exact (mul_le_mul_of_nonneg_left hkey hNpos.le).trans hfa

end StrongConv

end

theorem solution : type_of% @StrongConv.prob_norm_adjPerp_ge_le_dev :=
  @StrongConv.prob_norm_adjPerp_ge_le_dev
