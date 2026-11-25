-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:24:06.796463+00:00
-- url     : https://prove2.me/submissions/9e003ad0-e74c-4e84-ad13-4bbfbc27cbce

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArcSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_glue_unit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull__6a8fb3a1b1a4
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_indep_comp

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
theorem _root_.solution (hL' : L'.IsLB) (w : LB.Iso L' (L.pull F)) (w' : LB.Iso L'' (L'.pull F')) (hw : PGen w)
    (hw' : PGen w') (hL : L.IsLB) (hL'' : L''.IsLB) :
    ∃ w'' : LB.Iso L'' (L.pull (F' ≫ F)), Tri w w' w'' := by
  have hsub1 : ∀ (J : PUnit → L.ι) (k : L''.ι) (i : L'.ι),
      (L.pull (F' ≫ F)).U J ⊓ L''.U k ⊓ F' ⁻¹ᵁ L'.U i ≤ F' ⁻¹ᵁ ((L.pull F).U J ⊓ L'.U i) :=
    fun J k i x hx => ⟨mem_pull.2 (mem_pull₂.1 hx.1.1), hx.2⟩
  have hsub2 : ∀ (J : PUnit → L.ι) (k : L''.ι) (i : L'.ι),
      (L.pull (F' ≫ F)).U J ⊓ L''.U k ⊓ F' ⁻¹ᵁ L'.U i ≤ (L'.pull F').U (fun _ => i) ⊓ L''.U k :=
    fun J k i x hx => ⟨mem_pull.2 hx.2, hx.1.2⟩
  have hu : ∀ (J : PUnit → L.ι) (k : L''.ι) (i : L'.ι) {Y : Scheme.{0}} (f : Y ⟶ X'') (y : Y)
      (hy : f y ∈ (L.pull (F' ≫ F)).U J ⊓ L''.U k ⊓ F' ⁻¹ᵁ L'.U i),
      gm f y _ (res (hsub1 J k i) (pullU F' _ (w.s (J, i))) * res (hsub2 J k i) (w'.s (fun _ => i, k))) =
        gw w (f ≫ F') y (J PUnit.unit) i * gw w' f y i k := by
    intro J k i Y f y hy
    rw [map_mul]
    erw [gm_res f y _ hy, gm_res f y _ hy]
    congr 1
    exact gm_pull f F' y _ (hsub1 J k i hy) _
  have hs : ∀ p : (LB.div (L.pull (F' ≫ F)) L'').ι, ∃ s : Γ(X'', (L.pull (F' ≫ F)).U p.1 ⊓ L''.U p.2)ˣ,
      ∀ i, res (inf_le_left : (L.pull (F' ≫ F)).U p.1 ⊓ L''.U p.2 ⊓ F' ⁻¹ᵁ L'.U i ≤ _) s =
        res (hsub1 p.1 p.2 i) (pullU F' _ (w.s (p.1, i))) * res (hsub2 p.1 p.2 i) (w'.s (fun _ => i, p.2)) := by
    intro p
    refine glue_unit _ (fun i => (L.pull (F' ≫ F)).U p.1 ⊓ L''.U p.2 ⊓ F' ⁻¹ᵁ L'.U i)
      (fun i => inf_le_left) ?_ (fun i => res (hsub1 p.1 p.2 i) (pullU F' _ (w.s (p.1, i))) *
        res (hsub2 p.1 p.2 i) (w'.s (fun _ => i, p.2))) ?_
    · intro x hx
      obtain ⟨i, hi⟩ := exists_chart hL' (F' x)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, ⟨hx, hi⟩⟩
    · intro i i' x hx
      rw [hu p.1 p.2 i (𝟙 X'') x hx.1, hu p.1 p.2 i' (𝟙 X'') x hx.2]
      exact indep_comp w w' hw hw' hL hL'' (𝟙 X'') x (p.1 PUnit.unit) i i' p.2
        (mem_pull₂.1 hx.1.1.1) hx.1.2 hx.2.2 hx.1.1.2
  choose s hs using hs
  refine ⟨⟨s⟩, ?_⟩
  intro Y f y j i k hj hi hk
  have hy : f y ∈ (L.pull (F' ≫ F)).U (fun _ => j) ⊓ L''.U k ⊓ F' ⁻¹ᵁ L'.U i :=
    ⟨⟨mem_pull₂ (J := fun _ => j) |>.2 hj, hk⟩, hi⟩
  show gm f y _ (s (fun _ => j, k)) = _
  rw [← gm_res f y (inf_le_left : (L.pull (F' ≫ F)).U (fun _ => j) ⊓ L''.U k ⊓ F' ⁻¹ᵁ L'.U i ≤ _) hy,
    hs (fun _ => j, k) i, hu (fun _ => j) k i f y hy]
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
