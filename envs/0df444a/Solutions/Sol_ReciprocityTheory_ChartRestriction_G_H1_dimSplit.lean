-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.dimSplit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:26:35.965329+00:00
-- url     : https://prove2.me/submissions/23b716f4-2d7c-4de5-a125-e72162a1bfa9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_OneCHyp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_torus_dim
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_dim_unique
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_exists_dim
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_dim_base
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_torsor_pullback
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_pullback


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
namespace ReciprocityTheory.ChartRestriction.G.H1
theorem _root_.solution : DimSplitStatement := by
  intro E _ _ _ H V _ _ _ t P
  have := t.semi.smooth
  obtain ⟨n, W, hW, dW⟩ := exists_dim t.G.hom (eSec t.G (closedPoint V))
  have all : ∀ y : Sp V, eSec t.G y ∈ W := fun y =>
    (congrArg (fun U => y ∈ U) (Scheme.preimage_eq_top_of_closedPoint_mem (eSec t.G) hW)).mpr trivial
  have unit : ∀ {S' : Scheme.{0}} (b : S' ⟶ Sp V) (y : S'),
      pullback.fst t.G.hom b (eSec ((Over.pullback b).obj t.G) y) ∈ W := fun b y =>
    (congrArg (fun g => g y ∈ W) (cubeMapOf (isGrpPullback_pullback t.G b)).e_comm).mpr (all _)

  have g₁ : n = P.A.g := by
    have := P.A.smoothDim
    have : IsIso P.U.gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map P.U.gen.hom))
    have d : SmoothOfRelativeDimension (0 + P.A.g) (pullback.snd t.G.hom (jK V)) := by
      rw [show pullback.snd t.G.hom (jK V) = P.U.gen.hom.left ≫ P.A.A.hom from (Over.w P.U.gen.hom).symm]
      infer_instance
    exact (dim_base (IsPullback.of_hasPullback _ _) dW d _ (unit (jK V) (default : PrimeSpectrum (FractionRing V)))).trans
      (zero_add _)

  let c := P.U.gt 0
  have := c.q_hom
  have := c.i_hom
  have := c.q_flat
  have := c.q_surj
  have := c.q_affine
  have dT := torus_dim (Spec (CommRingCat.of (V ⧸ maximalIdeal V ^ (0 + 1)))) P.D.toPre.X
  have : Smooth c.q.left := by
    have := dT.smooth
    refine MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      ((torsor_pullback c.i c.q c.isKernel).map (Over.forget _)).flip ⟨⟨‹_›, ‹_›⟩, inferInstanceAs (QuasiCompact c.q.left)⟩ ?_
    exact smooth_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) this
  have : Nontrivial (V ⧸ maximalIdeal V ^ (0 + 1)) :=
    Ideal.Quotient.nontrivial_iff.2 (by rw [zero_add, pow_one]; exact (maximalIdeal.isMaximal V).ne_top)
  obtain ⟨y⟩ : Nonempty (Spec (CommRingCat.of (V ⧸ maximalIdeal V ^ (0 + 1)))) :=
    inferInstanceAs (Nonempty (PrimeSpectrum _))
  obtain ⟨m, W₁, hW₁, d₁⟩ := exists_dim c.q.left (eSec (thickObj V (maximalIdeal V) 0 t.G) y)
  have g₂ : m = Module.finrank ℤ P.D.toPre.X := dim_base (c.isKernel.map (Over.forget _)) d₁ dT (eSec _ y)
    ((congrArg (fun g => g.left y ∈ W₁) (IsMonHom.one_hom c.i)).mpr hW₁)
  have dB : SmoothOfRelativeDimension P.D.toPre.P.g (thickObj V (maximalIdeal V) 0 P.D.toPre.P.A).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _)
      P.D.toPre.P.smoothDim
  have d₂ : SmoothOfRelativeDimension (m + P.D.toPre.P.g) (W₁.ι ≫ (thickObj V (maximalIdeal V) 0 t.G).hom) := by
    rw [← Over.w c.q, ← Category.assoc]; infer_instance
  have d₃ : SmoothOfRelativeDimension n ((pullback.fst t.G.hom (thick V (maximalIdeal V) 0) ⁻¹ᵁ W).ι ≫
      (thickObj V (maximalIdeal V) 0 t.G).hom) := (smoothOfRelativeDimension_isStableUnderBaseChange n).of_isPullback
    ((isPullback_morphismRestrict _ W).paste_vert (IsPullback.of_hasPullback _ _)) dW
  have g₃ : n = m + P.D.toPre.P.g := by
    let W₂ := pullback.fst t.G.hom (thick V (maximalIdeal V) 0) ⁻¹ᵁ W
    have e₁ : SmoothOfRelativeDimension (0 + n) ((W₂ ⊓ W₁).ι ≫ (thickObj V (maximalIdeal V) 0 t.G).hom) := by
      rw [← Scheme.homOfLE_ι _ (inf_le_left : W₂ ⊓ W₁ ≤ W₂), Category.assoc]; infer_instance
    have e₂ : SmoothOfRelativeDimension (0 + (m + P.D.toPre.P.g)) ((W₂ ⊓ W₁).ι ≫ (thickObj V (maximalIdeal V) 0 t.G).hom) := by
      rw [← Scheme.homOfLE_ι _ (inf_le_right : W₂ ⊓ W₁ ≤ W₁), Category.assoc]; infer_instance
    simpa using dim_unique _ e₁ e₂ ⟨_, unit _ y, hW₁⟩
  rw [← g₁, g₃, g₂]
end ReciprocityTheory.ChartRestriction.G.H1
