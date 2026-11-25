-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.de_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:47:00.675175+00:00
-- url     : https://prove2.me/submissions/fb42c43a-7a01-46a3-a460-edf3adf57267

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscBDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TraceGramDetNeZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_trace_gram_det_ne_zero

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
theorem _root_.solution (hd : d.AxH 𝒜) (h : d.S1) : d.De hd h ≠ 0 := by
  classical
  letI alg : ∀ c, Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := fun c => (d.KTtoS h c).toAlgebra
  haveI : CharZero (KTf K d.D d.N) :=
    charZero_of_injective_algebraMap (algebraMap K (KTf K d.D d.N)).injective
  obtain ⟨_, hli, hsp⟩ := hd.a4.choose_spec
  have hS : ∀ c (p : KTp K d.D d.N),
      d.KTtoS h c (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) p) = d.sH c p := by
    intro c p
    unfold Data.KTtoS
    exact IsFractionRing.lift_algebraMap _ _
  have hsm : ∀ c (a : KTf K d.D d.N) (x : OmS (Ω c) d.D d.N), a • x = d.KTtoS h c a * x := by
    intro c a x
    rfl
  have hspan : ∀ y : ∀ c, OmS (Ω c) d.D d.N, ∃ μ : Fin d.del → KTf K d.D d.N,
      ∀ c, y c = ∑ k, μ k • d.bvecG hd.sel hd.a4.choose k c := by
    intro y
    obtain ⟨q, hq, p, hp⟩ := hsp y
    refine ⟨fun k => algebraMap _ (KTf K d.D d.N) (p k) / algebraMap _ (KTf K d.D d.N) q,
      fun c => ?_⟩
    simp only [hsm, map_div₀, hS]
    have hq' := hq c
    calc y c = (d.sH c q)⁻¹ * (d.sH c q * y c) := by
          rw [← mul_assoc, inv_mul_cancel₀ hq', one_mul]
      _ = (d.sH c q)⁻¹ * ∑ k, d.sH c (p k) * d.bvecG hd.sel hd.a4.choose k c :=
          congrArg (fun t => (d.sH c q)⁻¹ * t) (hp c)
      _ = ∑ k, d.sH c (p k) / d.sH c q * d.bvecG hd.sel hd.a4.choose k c := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
  have hind : ∀ v : Fin d.del → KTf K d.D d.N,
      (∀ c, ∑ l, v l • d.bvecG hd.sel hd.a4.choose l c = 0) → v = 0 := by
    intro v hv
    obtain ⟨⟨q, hq⟩, hqv⟩ :=
      IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (KTp K d.D d.N)) v
    have hqv' : ∀ l, ∃ pl : KTp K d.D d.N,
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) pl = q • v l := fun l => hqv l
    choose p hp using hqv'
    have hp0 := hli p (fun c => by
      have key := congrArg (fun t => d.KTtoS h c (algebraMap _ (KTf K d.D d.N) q) * t) (hv c)
      simp only [mul_zero, Finset.mul_sum] at key
      refine Eq.trans ?_ key
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hsm, ← mul_assoc, ← map_mul, ← Algebra.smul_def, ← hp l, hS]
      all_goals rfl)
    funext l
    have h1 : q • v l = 0 := by rw [← hp l, hp0 l, map_zero]
    rw [Algebra.smul_def] at h1
    have hq0 : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) q ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq
    exact (mul_eq_zero.mp h1).resolve_left hq0
  haveI hfd : ∀ c, FiniteDimensional (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := by
    intro c
    refine Module.finite_def.mpr ⟨Finset.univ.image (fun k => d.bvecG hd.sel hd.a4.choose k c),
      eq_top_iff.mpr fun y _ => ?_⟩
    obtain ⟨μ, hμ⟩ := hspan (Pi.single c y)
    have hy := hμ c
    rw [Pi.single_eq_same] at hy
    rw [hy]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  unfold Data.De
  exact trace_gram_det_ne_zero (fun k c => d.bvecG hd.sel hd.a4.choose k c) hind hspan
end ReciprocityTheory.ChartRestriction.G.T0.Data
