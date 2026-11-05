-- Prove2me | solution 1 for StrongConv.prob_norm_eval_sModel_ge_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-04T23:47:11.51717+00:00
-- url     : https://prove2.me/submissions/5a67fa6a-ec98-46cc-9858-28e9dd8aad6c

import Definitions.Def_StrongConv
import Theorems.Thm_StrongConv_exists_testFunction
import Theorems.Thm_StrongConv_norm_expTr_sub_trTau_le
import Theorems.Thm_StrongConv_exists_csDistribution_abs_expTr_sub_le
import Theorems.Thm_StrongConv_supp_subset_Icc_of_extends_nu_one
import Mathlib

section
section
open Polynomial Filter Topology

noncomputable section

namespace StrongConv.S9

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

end StrongConv.S9

end
end
end

section
section
open Polynomial Filter Topology

noncomputable section

namespace StrongConv.S9

open StrongConv
open scoped Matrix InnerProductSpace

section Part1
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem tr_tensorOp_apply {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (T : H →L[ℂ] H)
    (x : PiLp 2 (fun _ : Fin n => H)) (a : Fin m) :
    (tensorOp A T x) a = ∑ b, A a b • T (x b) := by
  simp [tensorOp, Pi.single_apply, eq_comm]

theorem tr_star_tensorOp {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (T : H →L[ℂ] H) :
    star (tensorOp A T) = tensorOp Aᴴ (star T) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp_rw [tr_tensorOp_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  simp [Matrix.conjTranspose_apply]

theorem tr_star_letterOp {d : ℕ} (u : Fin d → H →L[ℂ] H) (l : Fin d ⊕ Fin d) :
    star (letterOp u l) = letterOp u l.swap := by
  rcases l with i | i <;> simp [letterOp]

theorem tr_star_wordOp {d : ℕ} (u : Fin d → H →L[ℂ] H) (w : FreeMonoid (Fin d ⊕ Fin d)) :
    star (wordOp u w) = wordOp u (NCPoly.wordStar w) := by
  unfold wordOp NCPoly.wordStar
  induction w.toList using List.reverseRecOn with
  | nil => simp
  | append_singleton l a ih =>
    simp [star_mul, ih, tr_star_letterOp]

theorem tr_wordStar_involutive {d : ℕ} (w : FreeMonoid (Fin d ⊕ Fin d)) :
    NCPoly.wordStar (NCPoly.wordStar w) = w := by
  unfold NCPoly.wordStar
  simp [List.map_reverse, Function.comp_def]

end Part1

/-- `P(u, u*)` is self-adjoint for a self-adjoint `P` and any tuple `u` (the letter `sᵢ*` is
evaluated at `star (u i)`). -/
theorem eval_isSelfAdjoint {D d : ℕ} (P : NCPoly D d) (hP : P.IsSelfAdjoint)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (u : Fin d → H →L[ℂ] H) : IsSelfAdjoint (P.eval u) := by
  have hsupp : ∀ w, NCPoly.wordStar w ∈ P.support ↔ w ∈ P.support := by
    intro w
    rw [Finsupp.mem_support_iff, Finsupp.mem_support_iff, hP w]
    simp
  let e : FreeMonoid (Fin d ⊕ Fin d) ≃ FreeMonoid (Fin d ⊕ Fin d) :=
    ⟨NCPoly.wordStar, NCPoly.wordStar, tr_wordStar_involutive, tr_wordStar_involutive⟩
  unfold IsSelfAdjoint NCPoly.eval
  have hsum := fun (s : Finset (FreeMonoid (Fin d ⊕ Fin d))) (f : FreeMonoid (Fin d ⊕ Fin d) → (PiLp 2 (fun _ : Fin D => H) →L[ℂ] PiLp 2 (fun _ : Fin D => H))) => star_sum s f
  rw [hsum]
  have : ∑ w ∈ P.support, star (tensorOp (P w) (wordOp u w))
      = ∑ w ∈ P.support, tensorOp (P w) (wordOp u w) := by
    simp_rw [tr_star_tensorOp, tr_star_wordOp]
    refine Finset.sum_equiv e (fun w => (hsupp w).symm) ?_
    intro w hw
    simp only [e, Equiv.coe_fn_mk]
    rw [hP w]
  exact this




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

/-- Trace facts for `fnCalc χ Y`, `Y` self-adjoint on `D` copies of `{1_N}⊥`: nonnegative real part
if `χ ≥ 0`, and at least `1` if `‖Y‖ ≥ c > 0` and `χ = 1` on `{|x| ≥ c}`. -/
theorem trace_fnCalc_facts {D N : ℕ}
    (Y : PiLp 2 (fun _ : Fin D => OnesPerp N) →L[ℂ] PiLp 2 (fun _ : Fin D => OnesPerp N))
    (hY : IsSelfAdjoint Y) (χ : ℝ → ℝ) (hχc : Continuous χ) (h0 : ∀ x, 0 ≤ χ x) (c : ℝ)
    (hc : 0 < c) (h1 : ∀ x, c ≤ |x| → χ x = 1) :
    0 ≤ (LinearMap.trace ℂ _ ((fnCalc χ Y : PiLp 2 (fun _ : Fin D => OnesPerp N) →L[ℂ]
        PiLp 2 (fun _ : Fin D => OnesPerp N)) : PiLp 2 (fun _ : Fin D => OnesPerp N) →ₗ[ℂ]
        PiLp 2 (fun _ : Fin D => OnesPerp N))).re ∧
    (c ≤ ‖Y‖ → 1 ≤ (LinearMap.trace ℂ _ ((fnCalc χ Y : PiLp 2 (fun _ : Fin D => OnesPerp N) →L[ℂ]
        PiLp 2 (fun _ : Fin D => OnesPerp N)) : PiLp 2 (fun _ : Fin D => OnesPerp N) →ₗ[ℂ]
        PiLp 2 (fun _ : Fin D => OnesPerp N))).re) :=
  ⟨tr_trace_re_nonneg _ (tr_pos Y hY χ h0),
    fun hcY => tr_trace_re_ge_one Y hY χ hχc h0 c hc h1 hcY⟩

end StrongConv.S9

end
end
end

section
section
open Polynomial Filter Topology

noncomputable section

namespace StrongConv.S9

open StrongConv

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

/-- Markov: the probability that `‖P(Sᴺ,Sᴺ*)‖ ≥ c` is at most `D N` times `expTr χ`. -/
theorem prob_le_mul_expTr {D d : ℕ} (hD : 1 ≤ D) (N : ℕ) (hN : 1 ≤ N) (P : NCPoly D d)
    (hP : P.IsSelfAdjoint) (χ : ℝ → ℝ) (hχc : Continuous χ) (h0 : ∀ x, 0 ≤ χ x) (c : ℝ)
    (hc : 0 < c) (h1 : ∀ x, c ≤ |x| → χ x = 1) :
    uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) => c ≤ ‖P.eval (sModel σ)‖) ≤
      (D : ℝ) * N * expTr P N χ := by
  classical
  have hDN : ((D : ℝ) * N) ≠ 0 := by positivity
  set T : (Fin d → Equiv.Perm (Fin N)) → ℝ := fun σ =>
    (LinearMap.trace ℂ _ ((fnCalc χ (P.eval (sModel σ)) : PiLp 2 (fun _ : Fin D => OnesPerp N) →L[ℂ]
        PiLp 2 (fun _ : Fin D => OnesPerp N)) : PiLp 2 (fun _ : Fin D => OnesPerp N) →ₗ[ℂ]
        PiLp 2 (fun _ : Fin D => OnesPerp N))).re with hT
  have hfacts := fun σ : Fin d → Equiv.Perm (Fin N) =>
    trace_fnCalc_facts (P.eval (sModel σ)) (eval_isSelfAdjoint P hP _) χ hχc h0 c hc h1
  have hcard : (0 : ℝ) < Fintype.card (Fin d → Equiv.Perm (Fin N)) := by
    exact_mod_cast Fintype.card_pos
  have hexp : (D : ℝ) * N * expTr P N χ = (∑ σ, T σ) / Fintype.card (Fin d → Equiv.Perm (Fin N)) := by
    unfold expTr uniformExp trDN
    rw [mul_div_assoc', Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [hT]
    field_simp
  rw [hexp]
  unfold uniformProb
  rw [div_le_div_iff_of_pos_right hcard]
  calc ((Finset.univ.filter fun σ : Fin d → Equiv.Perm (Fin N) => c ≤ ‖P.eval (sModel σ)‖).card : ℝ)
      = ∑ σ ∈ Finset.univ.filter (fun σ : Fin d → Equiv.Perm (Fin N) => c ≤ ‖P.eval (sModel σ)‖),
          (1 : ℝ) := by simp
    _ ≤ ∑ σ ∈ Finset.univ.filter (fun σ : Fin d → Equiv.Perm (Fin N) => c ≤ ‖P.eval (sModel σ)‖), T σ := by
        apply Finset.sum_le_sum
        intro σ hσ
        exact (hfacts σ).2 (Finset.mem_filter.mp hσ).2
    _ ≤ ∑ σ, T σ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro σ _ _
        exact (hfacts σ).1

end StrongConv.S9

end
end
end

section
section
open Real

noncomputable section

namespace StrongConv.S9

/-- The real-number bookkeeping of the proof of Theorem 3.9. -/
theorem final_arith (C7 C4 Dr Nr q lg K ε : ℝ) (hD : 0 ≤ Dr) (hN : 1 ≤ Nr) (hq : 0 ≤ q)
    (hlg : Real.log 2 ≤ lg) (hε : 0 < ε) (hKε : ε < K) :
    Dr * Nr * (|C7| * ((4 * q * (1 + lg)) ^ 8 / Nr ^ 2) * (1 + Real.log (K / (ε / 2))) *
        ((C4 * 8) ^ 8 * (K / (ε / 2)) ^ ((8 : ℝ) + 1 / (1 + Real.log (K / (ε / 2)))))) ≤
      (|C7| * 4 ^ 8 * (1 + 1 / Real.log 2) ^ 8 * (1 + Real.log 2) * (C4 * 8) ^ 8 * 2 ^ 8 *
          Real.exp 1) * (Dr / Nr) * (K * q * lg / ε) ^ 8 * Real.log (Real.exp 1 * K / ε) := by
  have hK : 0 < K := hε.trans hKε
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlg0 : 0 < lg := hl2.trans_le hlg
  set r := K / ε with hr
  have hr1 : 1 < r := by rw [hr]; rw [lt_div_iff₀ hε]; linarith
  have hr0 : 0 < r := by linarith
  have h2r : K / (ε / 2) = 2 * r := by rw [hr]; field_simp
  rw [h2r]
  have hL : 0 < Real.log (2 * r) := Real.log_pos (by linarith)
  have hlogr : 0 < Real.log r := Real.log_pos hr1
  have hlog2r : Real.log (2 * r) = Real.log 2 + Real.log r := Real.log_mul (by norm_num) hr0.ne'
  have hlogeK : Real.log (Real.exp 1 * K / ε) = 1 + Real.log r := by
    rw [mul_div_assoc, ← hr, Real.log_mul (Real.exp_pos 1).ne' hr0.ne', Real.log_exp]
  rw [hlogeK]
  have e1 : (2 * r) ^ ((8 : ℝ) + 1 / (1 + Real.log (2 * r))) ≤ (2 * r) ^ 8 * Real.exp 1 := by
    rw [Real.rpow_add (by linarith)]
    have : (2 * r) ^ (1 / (1 + Real.log (2 * r))) ≤ Real.exp 1 := by
      rw [Real.rpow_def_of_pos (by linarith)]
      apply Real.exp_le_exp.mpr
      rw [mul_one_div]
      rw [div_le_one (by linarith)]
      linarith
    have h8 : (2 * r) ^ (8 : ℝ) = (2 * r) ^ (8 : ℕ) := by norm_cast
    rw [h8]
    gcongr
  have e2 : 1 + Real.log (2 * r) ≤ (1 + Real.log 2) * (1 + Real.log r) := by
    rw [hlog2r]; nlinarith
  have e3 : 1 + lg ≤ (1 + 1 / Real.log 2) * lg := by
    have : 1 ≤ lg / Real.log 2 := by rw [le_div_iff₀ hl2]; linarith
    calc 1 + lg ≤ lg / Real.log 2 + lg := by linarith
      _ = (1 + 1 / Real.log 2) * lg := by field_simp; ring
  have e3' : (1 + lg) ^ 8 ≤ ((1 + 1 / Real.log 2) * lg) ^ 8 :=
    pow_le_pow_left₀ (by linarith) e3 8
  have hN0 : 0 < Nr := by linarith
  have hC4 : 0 ≤ (C4 * 8) ^ 8 := by positivity
  have hpos2r : 0 ≤ (2 * r) ^ 8 := by positivity
  calc Dr * Nr * (|C7| * ((4 * q * (1 + lg)) ^ 8 / Nr ^ 2) * (1 + Real.log (2 * r)) *
        ((C4 * 8) ^ 8 * (2 * r) ^ ((8 : ℝ) + 1 / (1 + Real.log (2 * r)))))
      ≤ Dr * Nr * (|C7| * ((4 * q * ((1 + 1 / Real.log 2) * lg)) ^ 8 / Nr ^ 2) *
          ((1 + Real.log 2) * (1 + Real.log r)) *
          ((C4 * 8) ^ 8 * ((2 * r) ^ 8 * Real.exp 1))) := by
        gcongr
    _ = (|C7| * 4 ^ 8 * (1 + 1 / Real.log 2) ^ 8 * (1 + Real.log 2) * (C4 * 8) ^ 8 * 2 ^ 8 *
          Real.exp 1) * (Dr / Nr) * (K * q * lg / ε) ^ 8 * (1 + Real.log r) := by
        have : K * q * lg / ε = r * q * lg := by rw [hr]; field_simp
        rw [this]
        field_simp

end StrongConv.S9

end
end
end

section
section
open Polynomial Filter Topology

noncomputable section

namespace StrongConv.S9

open StrongConv

theorem eq_zero_of_abs_le_div (x X : ℝ) (hX : 0 ≤ X) (h : ∀ N : ℕ, 1 ≤ N → |x| ≤ X / N) : x = 0 := by
  by_contra hx
  have hpos : 0 < |x| := abs_pos.mpr hx
  obtain ⟨N, hN⟩ := exists_nat_gt (X / |x|)
  have hN1 : 1 ≤ N := by
    by_contra h1
    push Not at h1
    have : N = 0 := by omega
    subst this
    simp at hN
    have : 0 ≤ X / |x| := by positivity
    linarith
  have h2 := h N hN1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  rw [le_div_iff₀ hNpos] at h2
  rw [div_lt_iff₀ hpos] at hN
  linarith

theorem empty_event {D d : ℕ} (P : NCPoly D d) (N : ℕ) (hDN : D = 0 ∨ N = 0) (c : ℝ) (hc : 0 < c) :
    uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) => c ≤ ‖P.eval (sModel σ)‖) = 0 := by
  classical
  unfold uniformProb
  have hsub : Subsingleton (PiLp 2 (fun _ : Fin D => OnesPerp N)) := by
    rcases hDN with h | h
    · subst h
      refine ⟨fun x y => ?_⟩
      ext i
      exact i.elim0
    · subst h
      have : Subsingleton (OnesPerp 0) :=
        ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
      exact ⟨fun x y => PiLp.ext fun i => Subsingleton.elim _ _⟩
  have : ∀ σ : Fin d → Equiv.Perm (Fin N), ‖P.eval (sModel σ)‖ = 0 := by
    intro σ
    have : P.eval (sModel σ) = 0 := by
      exact ContinuousLinearMap.ext fun x => Subsingleton.elim _ _
    simp [this]
  simp [this, not_le.mpr hc]


theorem prob_norm_eval_sModel_ge_le_dev : ∃ C : ℝ, ∀ D d q₀ : ℕ, 2 ≤ d → ∀ P : NCPoly D d, P.IsSelfAdjoint →
    P.degree ≤ q₀ → ∀ ε : ℝ, 0 < ε → ε < P.fullNorm - ‖P.eval (sLimit d)‖ → ∀ N : ℕ,
      uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) =>
          ‖P.eval (sLimit d)‖ + ε ≤ ‖P.eval (sModel σ)‖) ≤
        C * (D / N) * (P.fullNorm * q₀ * Real.log d / ε) ^ 8 *
          Real.log (Real.exp 1 * P.fullNorm / ε) := by
  obtain ⟨C7, h7⟩ := exists_csDistribution_abs_expTr_sub_le
  obtain ⟨C4, h4⟩ := exists_testFunction
  obtain ⟨C5, h5⟩ := norm_expTr_sub_trTau_le
  refine ⟨|C7| * 4 ^ 8 * (1 + 1 / Real.log 2) ^ 8 * (1 + Real.log 2) * (C4 * 8) ^ 8 * 2 ^ 8 *
    Real.exp 1, ?_⟩
  intro D d q₀ hd P hP hdeg ε hε hεK N
  have hρ0 : 0 ≤ ‖P.eval (sLimit d)‖ := norm_nonneg _
  by_cases hDN : D = 0 ∨ N = 0
  · rw [empty_event P N hDN (‖P.eval (sLimit d)‖ + ε) (by linarith)]
    rcases hDN with h | h <;> simp [h]
  push Not at hDN
  obtain ⟨hD0, hN0⟩ := hDN
  have hD1 : 1 ≤ D := Nat.pos_of_ne_zero hD0
  have hN1 : 1 ≤ N := Nat.pos_of_ne_zero hN0
  generalize hρ : ‖P.eval (sLimit d)‖ = ρ at *
  generalize hK : P.fullNorm = K at *
  have hε2 : 0 < ε / 2 := by positivity
  obtain ⟨χ, hχs, hχ01, hχ0, hχ1, hχn⟩ := h4 8 K (ρ + ε / 2) (ε / 2) (by norm_num)
    (by linarith) (by linarith) hε2 (by linarith)
  have hχc : Continuous χ := hχs.continuous
  have h0 : ∀ x, 0 ≤ χ x := fun x => (hχ01 x).1
  obtain ⟨ν, hν, hν2⟩ := h7 P hP hdeg
  simp only [hK] at hν2
  let hs : smoothFun := ⟨χ, hχs⟩
  have hcoe : (hs : ℝ → ℝ) = χ := rfl
  have hχvan : ∀ x, |x| ≤ ρ + ε / 2 + ε / 2 / 2 → χ x = 0 := hχ0
  -- ν 1 kills χ
  have hsupp := supp_subset_Icc_of_extends_nu_one P hP (ν 1) (hν 1).1 (hν 1).2
  rw [hρ] at hsupp
  have hν1 : ν 1 hs = 0 :=
    eq_zero_of_supp_subset (ν 1) (hν 1).1 ρ (ε / 4) (by positivity) hsupp hs
      (fun x hx => hχvan x (by have := le_of_lt hx; linarith))
  -- the expansion with β = 2
  have hb2 : ∀ M : ℕ, 1 ≤ M → |expTr P M χ - ν 0 hs| ≤
      |C7 * (4 * q₀ * (1 + Real.log d)) ^ (4 * 2) / (M : ℝ) ^ 2 * conjExp 2 *
        lpNormCircle 2 (iteratedDeriv (4 * 2 + 1) (fun θ => χ (K * Real.cos θ)))| := by
    intro M hM
    have := hν2 M 2 hM le_rfl 2 (by norm_num) hs
    have hsum : ∑ i ∈ Finset.range 2, ν i hs / (M : ℝ) ^ i = ν 0 hs := by
      simp [Finset.sum_range_succ, hν1]
    rw [hsum] at this
    exact this.trans (le_abs_self _)
  -- ν 0 kills χ
  have hfn : fnCalc χ (P.eval (sLimit d)) = 0 :=
    fnCalc_eq_zero _ (eval_isSelfAdjoint P hP _) ρ (le_of_eq hρ) χ
      (fun x hx => hχvan x (by linarith))
  have hfn' : fnCalc (hs : ℝ → ℝ) (P.eval (sLimit d)) = 0 := hfn
  have htau : trTau (0 : PiLp 2 (fun _ : Fin D => L2Free d) →L[ℂ]
      PiLp 2 (fun _ : Fin D => L2Free d)) = 0 := by simp [trTau]
  set Mv : ℝ := C5 * (q₀ * (1 + Real.log d)) ^ 4 * conjExp 2 *
      lpNormCircle 2 (iteratedDeriv 5 (fun θ => χ (K * Real.cos θ))) + cNorm 0 χ (-K) K with hMv
  set Bv : ℝ := C7 * (4 * q₀ * (1 + Real.log d)) ^ (4 * 2) * conjExp 2 *
      lpNormCircle 2 (iteratedDeriv (4 * 2 + 1) (fun θ => χ (K * Real.cos θ))) with hBv
  have hM : ∀ M : ℕ, 1 ≤ M → |expTr P M χ| ≤ Mv / M := by
    intro M hM
    have := h5 P hP hdeg M hM 2 (by norm_num) hs
    simp only [hK] at this
    rw [hfn', htau, sub_zero, Complex.norm_real, Real.norm_eq_abs] at this
    refine this.trans (le_of_eq ?_)
    rw [hMv]
    change C5 * (q₀ * (1 + Real.log d)) ^ 4 / M * conjExp 2 *
        lpNormCircle 2 (iteratedDeriv 5 (fun θ => χ (K * Real.cos θ))) + cNorm 0 χ (-K) K / M = _
    ring
  have hν0 : ν 0 hs = 0 := by
    apply eq_zero_of_abs_le_div _ (|Mv| + |Bv|) (by positivity)
    intro M hM1
    have h1 := hb2 M hM1
    have h2 := hM M hM1
    have hMpos : (0 : ℝ) < M := by exact_mod_cast hM1
    have hM1' : (1 : ℝ) ≤ M := by exact_mod_cast hM1
    have e : C7 * (4 * q₀ * (1 + Real.log d)) ^ (4 * 2) / (M : ℝ) ^ 2 * conjExp 2 *
        lpNormCircle 2 (iteratedDeriv (4 * 2 + 1) (fun θ => χ (K * Real.cos θ))) =
        Bv / (M : ℝ) ^ 2 := by rw [hBv]; ring
    rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (M : ℝ) ^ 2)] at h1
    have h3 : |Bv| / (M : ℝ) ^ 2 ≤ |Bv| / M := by
      apply div_le_div_of_nonneg_left (abs_nonneg _) hMpos
      nlinarith
    have h4' : Mv / M ≤ |Mv| / M := by gcongr; exact le_abs_self _
    calc |ν 0 hs| = |expTr P M χ - (expTr P M χ - ν 0 hs)| := by ring_nf
      _ ≤ |expTr P M χ| + |expTr P M χ - ν 0 hs| := abs_sub _ _
      _ ≤ Mv / M + |Bv| / M := by linarith
      _ ≤ |Mv| / M + |Bv| / M := by linarith
      _ = (|Mv| + |Bv|) / M := by ring
  have hL1 : 1 < K / (ε / 2) := by rw [lt_div_iff₀ hε2]; linarith
  have hLpos : 0 < Real.log (K / (ε / 2)) := Real.log_pos hL1
  generalize hL : Real.log (K / (ε / 2)) = L at hLpos
  set β : ℝ := (1 + L) / L with hβ
  have hβ1 : 1 < β := by rw [hβ, lt_div_iff₀ hLpos]; linarith
  have hconj : conjExp β = 1 + L := by
    unfold conjExp; rw [hβ]; field_simp; ring
  have hlp := hχn β hβ1
  rw [hconj] at hlp
  simp only [Nat.cast_ofNat] at hlp
  have hb := hν2 N 2 hN1 le_rfl β hβ1 hs
  have hsum : ∑ i ∈ Finset.range 2, ν i hs / (N : ℝ) ^ i = 0 := by
    simp [Finset.sum_range_succ, hν0, hν1]
  rw [hsum, sub_zero] at hb
  have ha := (le_abs_self _).trans hb
  rw [hconj] at ha
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hlpnn : 0 ≤ lpNormCircle β (iteratedDeriv (4 * 2 + 1) (fun θ => χ (K * Real.cos θ))) :=
    ENNReal.toReal_nonneg
  have hSnn : 0 ≤ (4 * (q₀ : ℝ) * (1 + Real.log d)) ^ (4 * 2) / (N : ℝ) ^ 2 := by
    have : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ d))
    positivity
  have hkey : expTr P N χ ≤ |C7| * ((4 * (q₀ : ℝ) * (1 + Real.log d)) ^ 8 / (N : ℝ) ^ 2) *
      (1 + L) * ((C4 * 8) ^ 8 * (K / (ε / 2)) ^ ((8 : ℝ) + 1 / (1 + L))) := by
    refine ha.trans ?_
    have e : C7 * (4 * (q₀ : ℝ) * (1 + Real.log d)) ^ (4 * 2) / (N : ℝ) ^ 2 * (1 + L) *
        lpNormCircle β (iteratedDeriv (4 * 2 + 1) (fun θ => χ (K * Real.cos θ))) =
        C7 * (((4 * (q₀ : ℝ) * (1 + Real.log d)) ^ (4 * 2) / (N : ℝ) ^ 2) * (1 + L) *
        lpNormCircle β (iteratedDeriv (4 * 2 + 1) (fun θ => χ (K * Real.cos θ)))) := by ring
    rw [e]
    calc _ ≤ |C7| * (((4 * (q₀ : ℝ) * (1 + Real.log d)) ^ (4 * 2) / (N : ℝ) ^ 2) * (1 + L) *
        lpNormCircle β (iteratedDeriv (4 * 2 + 1) (fun θ => χ (K * Real.cos θ)))) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ |C7| * (((4 * (q₀ : ℝ) * (1 + Real.log d)) ^ (4 * 2) / (N : ℝ) ^ 2) * (1 + L) *
          ((C4 * 8) ^ 8 * (K / (ε / 2)) ^ ((8 : ℝ) + 1 / (1 + L)))) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          apply mul_le_mul_of_nonneg_left hlp (by positivity)
      _ = _ := by ring
  have hprob := prob_le_mul_expTr (D := D) hD1 N hN1 P hP χ hχc h0 (ρ + ε) (by linarith)
    (fun x hx => hχ1 x (by linarith))
  refine hprob.trans ?_
  have hlg : Real.log 2 ≤ Real.log d := Real.log_le_log (by norm_num) (by exact_mod_cast hd)
  have hfa := final_arith C7 C4 (D : ℝ) (N : ℝ) (q₀ : ℝ) (Real.log d) K ε (by positivity)
    (by exact_mod_cast hN1) (by positivity) hlg hε (by linarith)
  rw [hL] at hfa
  refine le_trans ?_ hfa
  have hDN0 : (0 : ℝ) ≤ (D : ℝ) * N := by positivity
  exact mul_le_mul_of_nonneg_left hkey hDN0

end StrongConv.S9

end
end
end

section
open StrongConv

theorem solution :
    ∃ C : ℝ, ∀ D d q₀ : ℕ, 2 ≤ d → ∀ P : NCPoly D d, P.IsSelfAdjoint → P.degree ≤ q₀ →
      ∀ ε : ℝ, 0 < ε → ε < P.fullNorm - ‖P.eval (sLimit d)‖ → ∀ N : ℕ,
      uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) =>
          ‖P.eval (sLimit d)‖ + ε ≤ ‖P.eval (sModel σ)‖) ≤
        C * (D / N) * (P.fullNorm * q₀ * Real.log d / ε) ^ 8 *
          Real.log (Real.exp 1 * P.fullNorm / ε) := by
  apply StrongConv.S9.prob_norm_eval_sModel_ge_le_dev <;> assumption

end
