-- Prove2me | solution 1 for PositivityTheory.ThKG.CayleyTransformDarboux.gen_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:05:54.084257+00:00
-- url     : https://prove2.me/submissions/feb71005-8792-4ee6-a411-fdcec7a22402

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreMain
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ToralCohomology_ShiftLow
import Theorems.Thm_PositivityTheory_ThKG_CayleyTransformDarboux_Lie_comm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open FockH1Action PositivityTheory.KReal
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.CayleyTransformDarboux
variable {A M : Type} [Ring A] [Algebra ℂ A] [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.ThKG.CayleyTransformDarboux
theorem _root_.solution {act : A →ₗ[ℂ] Module.End ℂ M} (h : Lie act) {g q l : Submodule ℂ A}
    (hg : ∀ X ∈ g, ∀ Y ∈ g, X * Y - Y * X ∈ g) (hq : q ≤ g) (hl : l ≤ g) (hs : g ≤ q ⊔ l) {V N : Submodule ℂ M}
    (hV : St act q V) (hVN : V ≤ N) (hN : St act l N) : ∃ W, V ≤ W ∧ W ≤ N ∧ St act g W := by
  have up : ∀ n, ∀ Z ∈ l, ∀ x ∈ filt act l V n, act Z x ∈ filt act l V (n + 1) := fun n Z hZ x hx =>
    Submodule.mem_sup_right (Submodule.mem_iSup_of_mem Z (Submodule.mem_iSup_of_mem hZ (Submodule.mem_map_of_mem hx)))
  have mono : ∀ n, filt act l V n ≤ filt act l V (n + 1) := fun n => le_sup_left
  have Q : ∀ n, St act q (filt act l V n) → ∀ Z ∈ g, ∀ x ∈ filt act l V n, act Z x ∈ filt act l V (n + 1) := by
    intro n hn Z hZ x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (hs hZ)
    rw [map_add, LinearMap.add_apply]
    exact add_mem (mono n (hn a ha x hx)) (up n b hb x hx)
  have P : ∀ n, St act q (filt act l V n) := by
    intro n
    induction n with
    | zero => exact hV
    | succ n ih =>
      intro Z hZ
      have : filt act l V (n + 1) ≤ (filt act l V (n + 1)).comap (act Z) := by
        refine sup_le (fun x hx => mono n (ih Z hZ x hx)) (iSup₂_le fun Y hY => ?_)
        rintro _ ⟨x, hx, rfl⟩
        rw [Submodule.mem_comap, h.comm]
        exact add_mem (up n Y hY _ (ih Z hZ x hx)) (Q n ih _ (hg Z (hq hZ) Y (hl hY)) x hx)
      exact fun x hx => this hx
  have le : ∀ n, filt act l V n ≤ N := by
    intro n
    induction n with
    | zero => exact hVN
    | succ n ih =>
      refine sup_le ih (iSup₂_le fun Y hY => ?_)
      rintro _ ⟨x, hx, rfl⟩
      exact hN Y hY x (ih hx)
  refine ⟨⨆ n, filt act l V n, le_iSup (filt act l V) 0, iSup_le le, fun Z hZ x hx => ?_⟩
  have : (⨆ n, filt act l V n) ≤ (⨆ n, filt act l V n).comap (act Z) :=
    iSup_le fun n y hy => Submodule.mem_iSup_of_mem (n + 1) (Q n (P n) Z hZ y hy)
  exact this hx
end PositivityTheory.ThKG.CayleyTransformDarboux
