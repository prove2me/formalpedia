-- Prove2me | solution 1 for SymBoolPCSP.CFixing.card_lt_of_subsets_true
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-06T19:08:34.133608+00:00
-- url     : https://prove2.me/submissions/296f56f5-e874-47e4-8745-3af48b2fb257

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic
import Theorems.Thm_FinsetParts_exists_parts_card_eq

open PCSPBLPAff.Symmetric Finset
namespace SymBoolPCSP.CFixing

/-- If every `m`-element subset `Z ⊆ I` has `f(e_Z) = 1` and at most `c` pairwise disjoint sets
can have `f(e_{S_i}) = 1`, then `|I| < m (c + 1)` (BG, proof of Lemma 4.12, Case 1). -/
theorem card_lt_of_subsets_true {L : ℕ} (f : (Fin L → Bool) → Bool) (c m : ℕ)
    (I : Finset (Fin L)) (hI : ∀ Z ⊆ I, Z.card = m → f (indicator Z) = true)
    (hdisj : ∀ (ℓ : ℕ) (S : Fin ℓ → Finset (Fin L)), (∀ i j, i ≠ j → Disjoint (S i) (S j)) →
      (∀ i, f (indicator (S i)) = true) → ℓ ≤ c) :
    I.card < m * (c + 1) := by
  classical
  by_contra h
  push_neg at h
  obtain ⟨J, hJI, hJc⟩ := Finset.exists_subset_card_eq h
  obtain ⟨Y, hYJ, hYc, hcov⟩ := FinsetParts.exists_parts_card_eq J (fun _ : Fin (c + 1) => m)
    (by simp [hJc, mul_comm])
  have := hdisj (c + 1) Y
    (fun i j hij => Finset.disjoint_left.mpr fun x hxi hxj =>
      hij (((hcov x (hYJ i hxi)).unique hxi hxj)))
    (fun i => hI (Y i) ((hYJ i).trans hJI) (hYc i))
  omega

end SymBoolPCSP.CFixing

open SymBoolPCSP.CFixing in
theorem solution {L : ℕ} (f : (Fin L → Bool) → Bool) (c m : ℕ)
    (I : Finset (Fin L)) (hI : ∀ Z ⊆ I, Z.card = m → f (indicator Z) = true)
    (hdisj : ∀ (ℓ : ℕ) (S : Fin ℓ → Finset (Fin L)), (∀ i j, i ≠ j → Disjoint (S i) (S j)) →
      (∀ i, f (indicator (S i)) = true) → ℓ ≤ c) :
    I.card < m * (c + 1) :=
  SymBoolPCSP.CFixing.card_lt_of_subsets_true f c m I hI hdisj
