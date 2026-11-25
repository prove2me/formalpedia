-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.sig_fprod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:25:00.158861+00:00
-- url     : https://prove2.me/submissions/a3580363-297c-4bd5-9a2f-3c670f90503d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscBDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UnitAtIntAt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_DePres
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AGFrameNonneg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GoodPrimesProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_BlockDegOfScale
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ProdZpowEqZpowSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Hartogs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FprodNeZero
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_algebraMap_K_KTf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_sigF_algebraMap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_translSEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_HDiscOmL_prod_zpow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_scale_multiHomogeneous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] BlockPoly.translEquiv_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.GaussGen.translSEquiv_apply



set_option autoImplicit false
set_option linter.style.haveILetI false
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
theorem _root_.solution (E : Ideal (KTp K d.D d.N) → ℤ) (hE : {q | q ∈ d.HtOne ∧ E q ≠ 0}.Finite)
    (hg : ∀ q ∈ d.HtOne, E q ≠ 0 → ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous
      (fun b : Fin (d.D + 1) => if b = 0 then 0 else d.dg (d.gen q)) (d.gen q))
    (bb : Fin (d.D + 1)) (u : Kˣ) :
    sigF (K := K) (D := d.D) (N := d.N) bb u (∏ᶠ (q : Ideal (KTp K d.D d.N)) (_ : q ∈ d.HtOne),
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen q) ^ E q) =
      algebraMap K (KTf K d.D d.N) (u : K) ^ (∑ᶠ (q : Ideal (KTp K d.D d.N)) (_ : q ∈ d.HtOne),
        E q * ((if bb = 0 then 0 else d.dg (d.gen q) : ℕ) : ℤ)) *
      ∏ᶠ (q : Ideal (KTp K d.D d.N)) (_ : q ∈ d.HtOne),
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen q) ^ E q := by
  classical
  have h1 : d.HtOne ∩ Function.mulSupport (fun q =>
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen q) ^ E q) ⊆ hE.toFinset := by
    rintro q ⟨hq, hs⟩
    rw [Set.Finite.coe_toFinset]
    exact ⟨hq, fun h0 => hs (by simp only [h0, zpow_zero])⟩
  have h1' : d.HtOne ∩ Function.support (fun q =>
      E q * ((if bb = 0 then 0 else d.dg (d.gen q) : ℕ) : ℤ)) ⊆ hE.toFinset := by
    rintro q ⟨hq, hs⟩
    rw [Set.Finite.coe_toFinset]
    exact ⟨hq, fun h0 => hs (by simp only [h0, zero_mul])⟩
  have h2 : (hE.toFinset : Set (Ideal (KTp K d.D d.N))) ⊆ d.HtOne := by
    intro q hq
    rw [Set.Finite.coe_toFinset] at hq
    exact hq.1
  rw [finprod_mem_eq_prod_of_subset _ h1 h2, finsum_mem_eq_sum_of_subset _ h1' h2, map_prod]
  have hκ : algebraMap K (KTf K d.D d.N) (u : K) ≠ 0 :=
    (map_ne_zero _).mpr u.ne_zero
  rw [← HDiscOmL.prod_zpow hκ, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun q hq => ?_
  have hq' : q ∈ d.HtOne ∧ E q ≠ 0 := by
    rw [Set.Finite.mem_toFinset] at hq
    exact hq
  have hs : sigP (N := d.N) bb u (d.gen q) =
      MvPolynomial.C ((u : K) ^ (if bb = 0 then 0 else d.dg (d.gen q))) * d.gen q :=
    scale_multiHomogeneous bb u (fun b : Fin (d.D + 1) => if b = 0 then 0 else d.dg (d.gen q))
      (d.gen q) (hg q hq'.1 hq'.2)
  have hs' : sigF (K := K) (D := d.D) (N := d.N) bb u
      (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen q)) =
      algebraMap K (KTf K d.D d.N) (u : K) ^ ((if bb = 0 then 0 else d.dg (d.gen q) : ℕ) : ℤ) *
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen q) := by
    rw [d.sigF_algebraMap, hs, map_mul, ← d.algebraMap_K_KTf, map_pow, zpow_natCast]
  rw [map_zpow₀, hs', mul_zpow, ← zpow_mul, mul_comm (E q)]
end ReciprocityTheory.ChartRestriction.G.T0.Data
