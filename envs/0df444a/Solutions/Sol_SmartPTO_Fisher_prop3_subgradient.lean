-- Prove2me | solution 1 for SmartPTO.Fisher.prop3_subgradient
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T17:50:28.445788+00:00
-- url     : https://prove2.me/submissions/3277dea1-a993-4ef0-88a1-cf5287fea1ec

import Mathlib
import Definitions.Def_SPOBounds_Natarajan_Model
import Definitions.Def_SmartPTO_Fisher_Setting
open scoped InnerProductSpace
open SmartPTO.Fisher
namespace SupportOracle
lemma maximum {d : ℕ} {S : Set (EuclideanSpace ℝ (Fin d))}
    {wstar : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hw : SPOBounds.Natarajan.IsOracle S wstar) (a : EuclideanSpace ℝ (Fin d)) :
    ∀ v ∈ S, ⟪a,v⟫_ℝ ≤ ⟪a,wstar (-a)⟫_ℝ := by
  intro v hv
  have h := (hw (-a)).2 v hv
  simp only [inner_neg_left] at h
  linarith
lemma bounded {d : ℕ} {S : Set (EuclideanSpace ℝ (Fin d))}
    {wstar : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hw : SPOBounds.Natarajan.IsOracle S wstar) (a : EuclideanSpace ℝ (Fin d)) :
    BddAbove ((fun v => ⟪a,v⟫_ℝ) '' S) := by
  refine ⟨⟪a,wstar (-a)⟫_ℝ,?_⟩
  rintro _ ⟨v,hv,rfl⟩
  exact maximum hw a v hv
lemma support_le {d : ℕ} {S : Set (EuclideanSpace ℝ (Fin d))}
    {wstar : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hw : SPOBounds.Natarajan.IsOracle S wstar) (a v : EuclideanSpace ℝ (Fin d)) (hv : v ∈ S) :
    ⟪a,v⟫_ℝ ≤ xi S a := le_csSup (bounded hw a) ⟨v,hv,rfl⟩
lemma support_eq {d : ℕ} {S : Set (EuclideanSpace ℝ (Fin d))}
    {wstar : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hw : SPOBounds.Natarajan.IsOracle S wstar) (a : EuclideanSpace ℝ (Fin d)) :
    xi S a = ⟪a,wstar (-a)⟫_ℝ := by
  apply le_antisymm
  · change sSup ((fun v => ⟪a,v⟫_ℝ) '' S) ≤ _
    have hne : ((fun v => ⟪a,v⟫_ℝ) '' S).Nonempty :=
      ⟨⟪a,wstar (-a)⟫_ℝ, wstar (-a),(hw (-a)).1,rfl⟩
    apply csSup_le hne
    rintro _ ⟨v,hv,rfl⟩
    exact maximum hw a v hv
  · exact support_le hw a _ (hw (-a)).1
end SupportOracle

theorem solution {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d)))
    (hSne : S.Nonempty) (hScpt : IsCompact S) (hScvx : Convex ℝ S)
    (wstar : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hw : SPOBounds.Natarajan.IsOracle S wstar)
    (c chat ct : EuclideanSpace ℝ (Fin d)) :
    spoPlusLoss S wstar chat c +
      ⟪(2 : ℝ) • (wstar c - wstar ((2 : ℝ) • chat - c)), ct - chat⟫_ℝ ≤
      spoPlusLoss S wstar ct c := by
  have he := SupportOracle.support_eq hw (c-(2:ℝ)•chat)
  simp only [neg_sub] at he
  have hl := SupportOracle.support_le hw (c-(2:ℝ)•ct)
    (wstar ((2:ℝ)•chat-c)) (hw ((2:ℝ)•chat-c)).1
  unfold spoPlusLoss
  rw [he]
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left] at *
  simp only [real_inner_comm] at *
  linarith
#print axioms solution
