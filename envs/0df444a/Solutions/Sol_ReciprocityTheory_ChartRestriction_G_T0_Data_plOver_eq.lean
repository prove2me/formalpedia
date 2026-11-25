-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.plOver_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:11:06.927549+00:00
-- url     : https://prove2.me/submissions/8fb82f3c-5779-4531-9813-b638fa255512

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValNorm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAE

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
theorem _root_.solution (h : d.S1) (la : HeightOneSpectrum (𝓞 K)) (c : ι) :
    letI : Algebra (Op d.D d.N la) (OmS (Ω c) d.D d.N) := d.algOp h la c
    d.PlOver la c = ValPl.PlacesOver (Op d.D d.N la) (OmS (Ω c) d.D d.N) := by
  letI : Algebra (Op d.D d.N la) (OmS (Ω c) d.D d.N) := d.algOp h la c
  have hOS : ∀ x : OT K d.D d.N, algebraMap (Op d.D d.N la) (OmS (Ω c) d.D d.N)
      (algebraMap (OT K d.D d.N) (Op d.D d.N la) x) = d.OTtoS c x := by
    intro x
    show d.KTtoS h c (OpToKT d.D d.N la (algebraMap _ _ x)) = _
    unfold OpToKT Data.KTtoS Data.OTtoS
    rw [IsLocalization.lift_eq, RingHom.comp_apply, IsFractionRing.lift_algebraMap]
    all_goals rfl
  ext w
  simp only [Data.PlOver, ValPl.PlacesOver, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hnd, hw⟩
    refine ⟨hnd, fun y => ?_⟩
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (laT d.D d.N la).primeCompl y
    have hs0 : w (d.OTtoS c s) = 0 := by
      have h1 := (hw s).1
      have h2 : ¬ 0 < w (d.OTtoS c s) := fun hlt =>
        (show (s : OT K d.D d.N) ∉ laT d.D d.N la from s.2) ((hw s).2.mp hlt)
      exact le_antisymm (not_lt.mp h2) h1
    have hmul : w (algebraMap _ (OmS (Ω c) d.D d.N) (IsLocalization.mk' (Op d.D d.N la) a s)) =
        w (d.OTtoS c a) := by
      have e : algebraMap _ (OmS (Ω c) d.D d.N) (IsLocalization.mk' (Op d.D d.N la) a s) *
          d.OTtoS c s = d.OTtoS c a := by
        rw [← hOS, ← hOS, ← map_mul, IsLocalization.mk'_spec]
      have := congrArg w e
      rw [AddValuation.map_mul, hs0, add_zero] at this
      exact this
    rw [hmul, IsLocalization.AtPrime.mk'_mem_maximal_iff (S := Op d.D d.N la) (I := laT d.D d.N la)]
    exact hw a
  · rintro ⟨hnd, hw⟩
    refine ⟨hnd, fun x => ?_⟩
    have := hw (algebraMap _ (Op d.D d.N la) x)
    have key : algebraMap (OT K d.D d.N) (Op d.D d.N la) x ∈ IsLocalRing.maximalIdeal (Op d.D d.N la) ↔
        x ∈ laT d.D d.N la := by
      first
        | exact IsLocalization.AtPrime.to_map_mem_maximal_iff (S := Op d.D d.N la)
            (I := laT d.D d.N la) x
        | (rw [← IsLocalization.mk'_one (M := (laT d.D d.N la).primeCompl) (Op d.D d.N la) x]
           exact IsLocalization.AtPrime.mk'_mem_maximal_iff (S := Op d.D d.N la)
            (I := laT d.D d.N la) x 1)
    rw [hOS, key] at this
    exact this
end ReciprocityTheory.ChartRestriction.G.T0.Data
