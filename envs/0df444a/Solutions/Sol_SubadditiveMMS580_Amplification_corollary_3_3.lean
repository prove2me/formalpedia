-- Prove2me | solution 1 for SubadditiveMMS580.Amplification.corollary_3_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T03:00:45.050302+00:00
-- url     : https://prove2.me/submissions/e57e7c1f-b2bb-4ec2-8859-7168d1d25d5e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SubadditiveMMS580_Amplification_Setting
import Definitions.Def_MultiAllocToAlloc_Subadditive_Valuation
import Definitions.Def_MultiAllocToAlloc_Subadditive_Allocation
import Definitions.Def_SubmodOrder_Subadditive
import Definitions.Def_LittleCharity_MMS_Setting
import Theorems.Thm_SubadditiveMMS580_Amplification_lemma_3_2

section
set_option autoImplicit false

open MultiAllocToAlloc.Subadditive

namespace SubadditiveMMS580.Amplification.Dev.C33

theorem mms_div {m : ℕ} (w : Finset (Fin m) → ℝ) (k : ℕ) (S : Finset (Fin m)) (c : ℝ)
    (hc : 0 < c) :
    LittleCharity.MMS.mms (fun T => w T / c) k S = LittleCharity.MMS.mms w k S / c := by
  classical
  unfold LittleCharity.MMS.mms
  simp only [div_eq_mul_inv]
  have : ∀ f : Fin m → Fin k, (⨅ j : Fin k, w (S.filter (fun g => f g = j)) * c⁻¹) =
      (⨅ j : Fin k, w (S.filter (fun g => f g = j))) * c⁻¹ := by
    intro f
    rw [mul_comm, Real.mul_iInf_of_nonneg (inv_nonneg.2 hc.le)]
    simp [mul_comm]
  simp_rw [this]
  rw [mul_comm, Real.mul_iSup_of_nonneg (inv_nonneg.2 hc.le)]
  simp [mul_comm]

theorem one_le_mms {m n : ℕ} (hn : 1 ≤ n) (w : Finset (Fin m) → ℝ) (hmono : IsMonotone w)
    (W : Fin n → Finset (Fin m)) (hW : SubadditiveMMS580.Amplification.IsValuableFamily w W) :
    1 ≤ LittleCharity.MMS.mms w n Finset.univ := by
  classical
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let f : Fin m → Fin n := fun x =>
    if h : ∃ r, x ∈ W r then Classical.choose h else ⟨0, hn⟩
  have hf : ∀ r, W r ⊆ Finset.univ.filter (fun g => f g = r) := by
    intro r x hx
    have h : ∃ r, x ∈ W r := ⟨r, hx⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, f, dif_pos h]
    by_contra hne
    exact Finset.disjoint_left.1 (hW.1 _ _ hne) (Classical.choose_spec h) hx
  unfold LittleCharity.MMS.mms
  refine le_trans ?_ (le_ciSup (f := fun f' : Fin m → Fin n =>
    ⨅ j : Fin n, w ((Finset.univ : Finset (Fin m)).filter (fun x => f' x = j)))
    (Set.finite_range _).bddAbove f)
  apply le_ciInf
  intro r
  exact le_trans (hW.2 r) (hmono _ _ (hf r))

end SubadditiveMMS580.Amplification.Dev.C33

namespace SubadditiveMMS580.Amplification
open SubadditiveMMS580.Amplification.Dev.C33 in
theorem chk_corollary_3_3 (u n : ℕ) (hu : 1 ≤ u) (hun : u ≤ n) {m : ℕ}
    (v : Fin u → Finset (Fin m) → ℝ)
    (hnorm : ∀ i, IsNormalized (v i)) (hmono : ∀ i, IsMonotone (v i))
    (hsub : ∀ i, SubmodOrder.Subadditive (v i))
    (W : Fin u → Fin n → Finset (Fin m)) (hW : ∀ i, IsValuableFamily (v i) (W i)) :
    ∃ A : Fin u → Finset (Fin m), IsAllocation A ∧
      (u : ℝ) * ((n / u : ℕ) : ℝ) / (((n / u : ℕ) : ℝ) + 1) ≤
        ((Finset.univ.filter (fun i => (1 : ℝ) / 2 ≤ v i (A i))).card : ℝ) := by
  classical
  have hn : 1 ≤ n := le_trans hu hun
  let lam : Fin u → ℝ := fun i => LittleCharity.MMS.mms (v i) n Finset.univ
  have hlam : ∀ i, 1 ≤ lam i := fun i => one_le_mms hn (v i) (hmono i) (W i) (hW i)
  let idx : Fin n → Fin u := fun j => if h : j.val < u then ⟨j.val, h⟩ else ⟨0, hu⟩
  let v' : Fin n → Finset (Fin m) → ℝ := fun j T => v (idx j) T / lam (idx j)
  have hpos : ∀ i, 0 < lam i := fun i => lt_of_lt_of_le one_pos (hlam i)
  have hcast : Fin.castLE hun = fun i : Fin u => (Fin.castLE hun i : Fin n) := rfl
  have hidx : ∀ i : Fin u, idx (Fin.castLE hun i) = i := by
    intro i
    simp [idx, i.2]
  obtain ⟨A, hA, hcount⟩ := lemma_3_2 n v'
    (fun j => by
      show v (idx j) ∅ / lam (idx j) = 0
      rw [(hnorm _ : v _ ∅ = 0), zero_div])
    (fun j S T hST => div_le_div_of_nonneg_right (hmono _ S T hST) (hpos _).le)
    (fun j S T => by
      have := hsub (idx j) S T
      have h2 := hpos (idx j)
      simp only [v']
      rw [← add_div]
      exact div_le_div_of_nonneg_right this h2.le)
    (fun j => by
      show LittleCharity.MMS.mms (fun T => v (idx j) T / lam (idx j)) n Finset.univ = 1
      rw [mms_div _ _ _ _ (hpos _)]
      exact div_self (hpos _).ne')
    (Finset.univ.filter (fun j : Fin n => j.val < u))
    ⟨⟨0, by omega⟩, by simp; omega⟩
  have hQcard : (Finset.univ.filter (fun j : Fin n => j.val < u)).card = u := by
    have : (Finset.univ.filter (fun j : Fin n => j.val < u)) =
        Finset.univ.image (Fin.castLE hun) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro h; exact ⟨⟨j.val, h⟩, by ext; simp⟩
      · rintro ⟨i, rfl⟩; simp
    rw [this, Finset.card_image_of_injective _ (Fin.castLE_injective hun)]
    simp
  refine ⟨fun i => A (Fin.castLE hun i), ?_, ?_⟩
  · intro i j hij
    exact hA _ _ (fun h => hij (Fin.castLE_injective hun h))
  · rw [hQcard] at hcount
    refine le_trans (le_of_eq (by ring)) (le_trans hcount ?_)
    have hsub' : (Finset.univ.filter (fun j : Fin n => j.val < u)).filter
        (fun j => (1 : ℝ) / 2 ≤ v' j (A j)) ⊆
        (Finset.univ.filter (fun i : Fin u => (1 : ℝ) / 2 ≤ v i (A (Fin.castLE hun i)))).image
          (Fin.castLE hun) := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image] at hj ⊢
      obtain ⟨hj1, hj2⟩ := hj
      refine ⟨⟨j.val, hj1⟩, ?_, by ext; simp⟩
      have hji : (Fin.castLE hun ⟨j.val, hj1⟩ : Fin n) = j := by ext; simp
      have e : idx j = ⟨j.val, hj1⟩ := by simp [idx, hj1]
      rw [hji]
      simp only [v', e] at hj2
      have hp := hpos ⟨j.val, hj1⟩
      rw [le_div_iff₀ hp] at hj2
      have := hlam ⟨j.val, hj1⟩
      have hv0 : 0 ≤ v ⟨j.val, hj1⟩ (A j) := by
        have := hmono ⟨j.val, hj1⟩ ∅ (A j) (Finset.empty_subset _)
        rwa [hnorm] at this
      nlinarith
    have := Finset.card_le_card hsub'
    rw [Finset.card_image_of_injective _ (Fin.castLE_injective hun)] at this
    exact_mod_cast this

end SubadditiveMMS580.Amplification
end

theorem solution : type_of% @SubadditiveMMS580.Amplification.chk_corollary_3_3 := @SubadditiveMMS580.Amplification.chk_corollary_3_3
