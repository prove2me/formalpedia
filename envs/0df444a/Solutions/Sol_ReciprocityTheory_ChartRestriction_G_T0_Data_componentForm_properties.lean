-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.componentForm_properties
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:42:51.509841+00:00
-- url     : https://prove2.me/submissions/45de5644-a58d-4091-81bf-12b50df313ee

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GeneratorNeZeroOfHeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_DegreeSumIdentity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SpecialFibreFactorization
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ComponentFormProperties
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_DegreeSumIdentity
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_SpecialFibreFactorization
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_componentForm_poly


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
theorem _root_.solution (hd : d.AxH 𝒜) (h : d.S1) (c : ι) :
    ∃ F : KTp K d.D d.N, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c ∧ F ≠ 0 ∧
      ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => d.delc c) F ∧
      (∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
        d.nPMM h c (d.w (d.jc c) c) p * (d.dg (d.gen p) : ℤ)) = d.delc c ∧
      ∀ x : Fin (d.N + 1) → K, d.wx x c ≠ 0 → ∃ κ : K, κ ≠ 0 ∧
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N)
          (MvPolynomial.aeval (fun v : TVar d.D d.N =>
            if v.1 = 0 then MvPolynomial.C (x v.2) else MvPolynomial.X v) F) =
        algebraMap K (KTf K d.D d.N) κ *
          ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
            algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ d.nPMM h c (d.wx x c) p := by
  obtain ⟨F, hF, hF0⟩ := d.componentForm_poly hd h c
  obtain ⟨hmh, hmm⟩ := d.DegreeSumIdentity hd h c F hF
  exact ⟨F, hF, hF0, hmh, hmm, fun x hx => d.SpecialFibreFactorization hd h c F hF x hx⟩
end ReciprocityTheory.ChartRestriction.G.T0.Data
