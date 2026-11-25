-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_cancel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:27:21.366695+00:00
-- url     : https://prove2.me/submissions/d2a50fc8-1007-4494-ba0c-b3e9185a6964

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArcSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_glue_unit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull__6a8fb3a1b1a4
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_indep_cancel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X X' X'' : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} {F : X' ⟶ X} {F' : X'' ⟶ X'}
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution (hL : L.IsLB) (w : LB.Iso L' (L.pull F)) (w'' : LB.Iso L'' (L.pull (F' ≫ F))) (hw : PGen w)
    (hw'' : PGen w'') (hL' : L'.IsLB) (hL'' : L''.IsLB) :
    ∃ w' : LB.Iso L'' (L'.pull F'), Tri w w' w'' := by
  have hsub1 : ∀ (I : PUnit → L'.ι) (k : L''.ι) (j : L.ι),
      (L'.pull F').U I ⊓ L''.U k ⊓ F' ⁻¹ᵁ (F ⁻¹ᵁ L.U j) ≤
        F' ⁻¹ᵁ ((L.pull F).U (fun _ => j) ⊓ L'.U (I PUnit.unit)) :=
    fun I k j x hx => ⟨mem_pull.2 hx.2, mem_pull.1 hx.1.1⟩
  have hsub2 : ∀ (I : PUnit → L'.ι) (k : L''.ι) (j : L.ι),
      (L'.pull F').U I ⊓ L''.U k ⊓ F' ⁻¹ᵁ (F ⁻¹ᵁ L.U j) ≤ (L.pull (F' ≫ F)).U (fun _ => j) ⊓ L''.U k :=
    fun I k j x hx => ⟨mem_pull₂.2 hx.2, hx.1.2⟩
  have hu : ∀ (I : PUnit → L'.ι) (k : L''.ι) (j : L.ι) {Y : Scheme.{0}} (f : Y ⟶ X'') (y : Y)
      (hy : f y ∈ (L'.pull F').U I ⊓ L''.U k ⊓ F' ⁻¹ᵁ (F ⁻¹ᵁ L.U j)),
      gm f y _ ((res (hsub1 I k j) (pullU F' _ (w.s (fun _ => j, I PUnit.unit))))⁻¹ *
          res (hsub2 I k j) (w''.s (fun _ => j, k))) =
        (gw w (f ≫ F') y j (I PUnit.unit))⁻¹ * gw w'' f y j k := by
    intro I k j Y f y hy
    rw [map_mul, map_inv]
    erw [gm_res f y _ hy, gm_res f y _ hy]
    congr 2
    exact gm_pull f F' y _ (hsub1 I k j hy) _
  have hs : ∀ p : (LB.div (L'.pull F') L'').ι, ∃ s : Γ(X'', (L'.pull F').U p.1 ⊓ L''.U p.2)ˣ,
      ∀ j, res (inf_le_left : (L'.pull F').U p.1 ⊓ L''.U p.2 ⊓ F' ⁻¹ᵁ (F ⁻¹ᵁ L.U j) ≤ _) s =
        (res (hsub1 p.1 p.2 j) (pullU F' _ (w.s (fun _ => j, p.1 PUnit.unit))))⁻¹ *
          res (hsub2 p.1 p.2 j) (w''.s (fun _ => j, p.2)) := by
    intro p
    refine glue_unit _ (fun j => (L'.pull F').U p.1 ⊓ L''.U p.2 ⊓ F' ⁻¹ᵁ (F ⁻¹ᵁ L.U j))
      (fun j => inf_le_left) ?_ (fun j => (res (hsub1 p.1 p.2 j) (pullU F' _ (w.s (fun _ => j, p.1 PUnit.unit))))⁻¹ *
          res (hsub2 p.1 p.2 j) (w''.s (fun _ => j, p.2))) ?_
    · intro x hx
      obtain ⟨j, hj⟩ := exists_chart hL (F (F' x))
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, ⟨hx, hj⟩⟩
    · intro j j' x hx
      rw [hu p.1 p.2 j (𝟙 X'') x hx.1, hu p.1 p.2 j' (𝟙 X'') x hx.2]
      exact indep_cancel w w'' hw hw'' hL' hL'' (𝟙 X'') x j j' (p.1 PUnit.unit) p.2
        hx.1.2 hx.2.2 (mem_pull.1 hx.1.1.1) hx.1.1.2
  choose s hs using hs
  refine ⟨⟨s⟩, ?_⟩
  intro Y f y j i k hj hi hk
  have hy : f y ∈ (L'.pull F').U (fun _ => i) ⊓ L''.U k ⊓ F' ⁻¹ᵁ (F ⁻¹ᵁ L.U j) :=
    ⟨⟨mem_pull (J := fun _ => i) |>.2 hi, hk⟩, hj⟩
  show _ = _ * gm f y _ (s (fun _ => i, k))
  rw [← gm_res f y (inf_le_left : (L'.pull F').U (fun _ => i) ⊓ L''.U k ⊓ F' ⁻¹ᵁ (F ⁻¹ᵁ L.U j) ≤ _) hy,
    hs (fun _ => i, k) j, hu (fun _ => i) k j f y hy, mul_inv_cancel_left]
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
