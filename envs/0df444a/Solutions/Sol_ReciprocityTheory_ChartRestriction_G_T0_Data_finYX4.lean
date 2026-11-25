-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.finYX4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:26:13.199175+00:00
-- url     : https://prove2.me/submissions/6738c2ae-3f8d-4d3c-b30b-f383640057b1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_BasisExtend
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FracFieldPositiveRowsOmega
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_DecompBlock0
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_fieldEquiv_compat_liftY


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
set_option synthInstance.maxHeartbeats 400000
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (hd : d.AxH 𝒜) (h : d.S1) (c : ι) :
    letI := d.algLE h c
    letI := (VariableBasisExtension.liftY (L := d.FracFieldPositiveRowsBase) (E := d.FracFieldPositiveRowsOmega c) (σ := Fin (d.N + 1))).toAlgebra
    FiniteDimensional (FractionRing (MvPolynomial (Fin (d.N + 1)) d.FracFieldPositiveRowsBase))
      (FractionRing (MvPolynomial (Fin (d.N + 1)) (d.FracFieldPositiveRowsOmega c))) := by
  letI := d.algLE h c
  letI := (VariableBasisExtension.liftY (L := d.FracFieldPositiveRowsBase) (E := d.FracFieldPositiveRowsOmega c) (σ := Fin (d.N + 1))).toAlgebra
  letI := (d.KTtoS h c).toAlgebra
  haveI : FiniteDimensional (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := by
    classical
    obtain ⟨e, -, -, hsp⟩ := hd.a4
    refine ⟨⟨Finset.univ.image (fun k : Fin d.del => algebraMap (Ω c) (OmS (Ω c) d.D d.N)
      (ratio (Ω := Ω c) (d.thp (hd.sel k) c) (e c))), ?_⟩⟩
    rw [eq_top_iff]
    intro y _
    obtain ⟨q, hq, p, hp⟩ := hsp (fun c' => if hc : c' = c then hc ▸ y else 0)
    have hpc : d.sH c q * y = ∑ k, d.sH c (p k) * algebraMap (Ω c) (OmS (Ω c) d.D d.N)
        (ratio (Ω := Ω c) (d.thp (hd.sel k) c) (e c)) := by
      have h1 := hp c
      first
        | (simp only [dif_pos (rfl : c = c)] at h1; exact h1)
        | simpa using h1
    have hq0 := hq c
    have hKT : ∀ r : KTp K d.D d.N, d.KTtoS h c (algebraMap _ _ r) = d.sH c r := fun r => by
      simp [Data.KTtoS]
    have hy : y = ∑ k, (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (p k) /
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) q) •
        algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.thp (hd.sel k) c) (e c)) := by
      simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_div₀, hKT,
        div_mul_eq_mul_div, ← Finset.sum_div, ← hpc]
      first
        | exact (mul_div_cancel_left₀ y hq0).symm
        | field_simp
    rw [hy]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_univ k))))
  exact Module.Finite.of_equiv_equiv d.eLX4 (d.eEX4 c)
    (RingHom.ext fun q => (d.fieldEquiv_compat_liftY h c q).symm)
end ReciprocityTheory.ChartRestriction.G.T0.Data
