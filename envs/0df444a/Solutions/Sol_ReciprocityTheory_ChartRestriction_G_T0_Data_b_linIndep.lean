-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.b_linIndep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:12:21.253475+00:00
-- url     : https://prove2.me/submissions/446fe8f7-7176-46de-8a5a-e499c1c0b09f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField IsDedekindDomain
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (hd : d.AxH 𝒜) (h : d.S1) :
    letI : ∀ c, Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := fun c => (d.KTtoS h c).toAlgebra
    LinearIndependent (KTf K d.D d.N) (d.bvecG hd.sel hd.a4.choose) := by
  letI : ∀ c, Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := fun c => (d.KTtoS h c).toAlgebra
  classical
  obtain ⟨-, hind, -⟩ := hd.a4.choose_spec
  rw [Fintype.linearIndependent_iff]
  intro q hq
  obtain ⟨⟨s, hs⟩, hint⟩ :=
    IsLocalization.exist_integer_multiples (nonZeroDivisors (KTp K d.D d.N)) Finset.univ q
  choose p hp using fun k => hint k (Finset.mem_univ k)
  have hsH : ∀ c (x : KTp K d.D d.N),
      d.sH c x = d.KTtoS h c (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) x) := by
    intro c x
    rw [Data.KTtoS, IsFractionRing.lift_algebraMap]
    rfl
  have hzero : ∀ k, p k = 0 := hind p (fun c => by
    have hc := congrFun hq c
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply] at hc
    simp only [Algebra.smul_def] at hc
    calc ∑ k, d.sH c (p k) * algebraMap (Ω c) (OmS (Ω c) d.D d.N)
            (ratio (Ω := Ω c) (d.thp (hd.sel k) c) (hd.a4.choose c))
        = d.KTtoS h c (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) s) *
            ∑ k, algebraMap (KTf K d.D d.N) (OmS (Ω c) d.D d.N) (q k) *
              d.bvecG hd.sel hd.a4.choose k c := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hsH, hp k, Algebra.smul_def, map_mul, mul_assoc]
          rfl
      _ = 0 := by rw [hc, mul_zero])
  intro k
  have hk := hp k
  rw [hzero k, map_zero, Algebra.smul_def] at hk
  exact (mul_eq_zero.mp hk.symm).resolve_left
    (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs)
end ReciprocityTheory.ChartRestriction.G.T0.Data
