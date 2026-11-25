-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.ae_evT_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:29:10.817777+00:00
-- url     : https://prove2.me/submissions/e69f630b-5636-414e-bd93-95c3bd7e3e31

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscBDefs
import Definitions.Def_ReciprocityTheory_SemistableReduction_LogNormCoeffSubLeBlockSphereLogMean
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AeEvTNeZero
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_Closed_sj
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_Closed_sphereLogIntegrable
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_blockSphere_logMean_bound
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_eval_mul_of_isMultiHomogeneous
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_exists_torus_coeff_le
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_null_of_logBound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (sg : K →+* ℂ) (q : KTp K d.D d.N) (hq : q ≠ 0) (m : Fin (d.D + 1) → ℕ)
    (hm : m 0 = 0) (hqm : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous m q) :
    ∀ᵐ z ∂(ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)), d.evT sg 0 (d.tOf z) q ≠ 0 := by
  classical
  have hnpos : 0 < d.N + 1 := Nat.succ_pos _
  have hqm' : ∀ s ∈ q.support, ∀ b, ∑ j, s (b, j) = m b := hqm

  let ψ : Fin d.D × Fin (d.N + 1) → TVar d.D d.N := fun p => (p.1.succ, p.2)
  have hψ : Function.Injective ψ := by
    intro p p' h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    exact Prod.ext (Fin.succ_injective _ h1) h2
  have hvars : (q.vars : Set (TVar d.D d.N)) ⊆ Set.range ψ := by
    intro v hv
    rcases v with ⟨i, j⟩
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨k, rfl⟩
    · exfalso
      obtain ⟨s, hs, hsv⟩ := (MvPolynomial.mem_vars _).1 (Finset.mem_coe.1 hv)
      have h0 := hqm' s hs 0
      rw [hm] at h0
      have hz : s ((0 : Fin (d.D + 1)), j) = 0 :=
        (Finset.sum_eq_zero_iff.1 h0) j (Finset.mem_univ j)
      exact (Finsupp.mem_support_iff.1 hsv) hz
    · exact ⟨(k, j), rfl⟩
  obtain ⟨q', hq'⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range q ψ hψ hvars
  obtain ⟨g, hgdef⟩ : ∃ g : MvPolynomial (Fin d.D × Fin (d.N + 1)) ℂ,
      g = MvPolynomial.map sg q' := ⟨_, rfl⟩

  have hev : ∀ z, d.evT sg 0 (d.tOf z) q = MvPolynomial.eval (ReciprocityTheory.MultiplicativeHeights.blockPoint z) g := by
    intro z
    rw [hgdef, MvPolynomial.eval_map, ← hq']
    unfold ReciprocityTheory.ChartRestriction.G.T0.Data.evT
    rw [MvPolynomial.eval₂_rename]
    congr 1

  have hg : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun b : Fin d.D => m b.succ) g := by
    unfold ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous
    intro s hs b
    have hs' : MvPolynomial.coeff s q' ≠ 0 := by
      rw [hgdef, MvPolynomial.mem_support_iff, MvPolynomial.coeff_map] at hs
      intro h0
      rw [h0, map_zero] at hs
      exact hs rfl
    have hmem : Finsupp.mapDomain ψ s ∈ q.support := by
      rw [MvPolynomial.mem_support_iff, ← hq', MvPolynomial.coeff_rename_mapDomain ψ hψ]
      exact hs'
    exact (Finset.sum_congr rfl fun j _ => (Finsupp.mapDomain_apply hψ s (b, j)).symm).trans
      (hqm' _ hmem b.succ)

  have hg0 : g ≠ 0 := by
    rw [hgdef]
    intro h
    apply hq
    rw [← hq']
    have h' : q' = 0 := MvPolynomial.map_injective (f := sg) sg.injective (by rw [h, map_zero])
    rw [h', map_zero]

  obtain ⟨s, hs⟩ := MvPolynomial.ne_zero_iff.1 hg0
  obtain ⟨z, hz1, hzle⟩ := ReciprocityTheory.MultiplicativeHeights.exists_torus_coeff_le g s
  have hz0 : MvPolynomial.eval z g ≠ 0 := by
    intro h
    rw [h, norm_zero] at hzle
    exact hs (norm_le_zero_iff.1 hzle)
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (Real.sqrt ((d.N + 1 : ℕ) : ℝ))⁻¹ := ⟨_, rfl⟩
  have hrpos : 0 < r := by
    rw [hr]
    exact inv_pos.2 (Real.sqrt_pos.2 (Nat.cast_pos.2 hnpos))
  have hvec : ∀ b : Fin d.D, (WithLp.toLp 2 (fun j : Fin (d.N + 1) => (r : ℂ) * z (b, j)) :
      EuclideanSpace ℂ (Fin (d.N + 1))) ∈ Metric.sphere (0 : EuclideanSpace ℂ (Fin (d.N + 1))) 1 := by
    intro b
    rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq]
    have hterm : ∀ j : Fin (d.N + 1), ‖(WithLp.toLp 2 (fun j : Fin (d.N + 1) => (r : ℂ) * z (b, j)) :
        EuclideanSpace ℂ (Fin (d.N + 1))) j‖ ^ 2 = r ^ 2 := by
      intro j
      show ‖(r : ℂ) * z (b, j)‖ ^ 2 = r ^ 2
      rw [norm_mul, hz1, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos]
    rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, hr, inv_pow, Real.sq_sqrt (Nat.cast_nonneg _),
      mul_inv_cancel₀ (Nat.cast_pos.2 hnpos).ne', Real.sqrt_one]
  let u : ReciprocityTheory.MultiplicativeHeights.BlockSphere d.D (d.N + 1) := fun b => ⟨_, hvec b⟩
  have hu : MvPolynomial.eval (ReciprocityTheory.MultiplicativeHeights.blockPoint u) g ≠ 0 := by
    have hbp : ReciprocityTheory.MultiplicativeHeights.blockPoint u = fun p => (r : ℂ) * z p := by
      funext p
      rfl
    rw [hbp, ReciprocityTheory.MultiplicativeHeights.eval_mul_of_isMultiHomogeneous hg]
    exact mul_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.2 hrpos.ne')) hz0

  have key := ReciprocityTheory.MultiplicativeHeights.null_of_logBound hnpos ReciprocityTheory.MultiplicativeHeights.Closed.sphereLogIntegrable
    (ReciprocityTheory.MultiplicativeHeights.blockSphere_logMean_bound ReciprocityTheory.MultiplicativeHeights.Closed.sj ReciprocityTheory.MultiplicativeHeights.Closed.sphereLogIntegrable
      hnpos d.D) _ g u hg hu
  rw [MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null ?_ key
  intro w hw
  simp only [Set.mem_setOf_eq, not_not] at hw ⊢
  rw [← hev w]
  exact hw
end ReciprocityTheory.ChartRestriction.G.T0.Data
