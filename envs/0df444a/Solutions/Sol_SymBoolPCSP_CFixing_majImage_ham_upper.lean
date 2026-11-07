-- Prove2me | solution 1 for SymBoolPCSP.CFixing.majImage_ham_upper
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-06T09:09:22.313952+00:00
-- url     : https://prove2.me/submissions/4ac0bcab-f9b0-42e6-85d1-eccd42475813

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic

open PCSPBLPAff.Symmetric Finset
namespace SymBoolPCSP.CFixing

namespace Aux_majImage_ham_upper

theorem hw_decide_mem {k : ℕ} (T : Finset (Fin k)) : hw (fun c => decide (c ∈ T)) = T.card := by
  unfold hw; congr 1; ext c; simp

theorem hw_prefix {k b : ℕ} (hb : b ≤ k) : hw (fun c : Fin k => decide (c.val < b)) = b := by
  unfold hw
  rw [← Finset.card_map Fin.valEmbedding]
  convert Finset.card_range b using 2
  ext n; simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    decide_eq_true_eq, Fin.valEmbedding_apply, Finset.mem_range]
  constructor
  · rintro ⟨c, hc, rfl⟩; exact hc
  · intro hn; exact ⟨⟨n, by omega⟩, hn, rfl⟩

theorem maj_construction {k : ℕ} {S : Set ℕ} (R0 : Fin k → Bool) (hR0 : hw R0 ∈ S)
    (r q a b : ℕ) (ha : a ∈ S) (hab : a ≤ b) (hbk : b ≤ k) (hb : 0 < b)
    (hL : Odd (r + q * b)) :
    (fun c : Fin k => decide (r + q * b < 2 * ((if R0 c then r else 0) +
      (if c.val < b then q * a else 0)))) ∈ MajImage (Ham k S) := by
  have : NeZero b := ⟨hb.ne'⟩
  obtain ⟨G, -, hG⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin b)))
    (n := a) (by simpa using hab)
  let F : Fin b → Finset (Fin b) := fun j => G.map (Equiv.addRight j).toEmbedding
  let emb : Fin b ↪ Fin k := Fin.castLEEmb hbk
  let cyc : Fin b → Fin k → Bool := fun j c => decide (c ∈ (F j).map emb)
  have hcyc : ∀ j, hw (cyc j) = a := fun j => by
    simp only [cyc, hw_decide_mem, Finset.card_map, F, hG]
  let g : Fin r ⊕ (Fin q × Fin b) → Fin k → Bool := Sum.elim (fun _ => R0) (fun p => cyc p.2)
  let e : Fin (r + q * b) ≃ Fin r ⊕ (Fin q × Fin b) :=
    finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl _) finProdFinEquiv.symm)
  refine ⟨r + q * b, hL, fun i => g (e i), fun i => ?_, ?_⟩
  · show hw (g (e i)) ∈ S
    rcases e i with i' | p
    · exact hR0
    · show hw (cyc p.2) ∈ S
      rw [hcyc]; exact ha
  · funext c
    simp only [Maj]
    congr 2
    have hcnt : ∑ j : Fin b, (if cyc j c = true then 1 else 0) =
        if c.val < b then a else 0 := by
      split_ifs with hcb
      · let c' : Fin b := ⟨c.val, hcb⟩
        have hmem : ∀ j, (cyc j c = true) ↔ (c' - j ∈ G) := fun j => by
          have : c = emb c' := Fin.ext rfl
          simp only [cyc, decide_eq_true_eq, this, Finset.mem_map' emb, F,
            Finset.mem_map_equiv, Equiv.coe_addRight, Equiv.addRight_symm, sub_eq_add_neg]
        simp only [hmem]
        rw [Fintype.sum_equiv (Equiv.subLeft c') (fun j => if c' - j ∈ G then 1 else 0)
          (fun g' => if g' ∈ G then 1 else 0) (fun j => rfl)]
        rw [Finset.sum_boole]; simp [hG]
      · refine Finset.sum_eq_zero (fun j _ => ?_)
        have : cyc j c = false := by
          simp only [cyc, decide_eq_false_iff_not, Finset.mem_map]
          rintro ⟨x, -, hx⟩
          apply hcb; rw [← hx]; simp [emb]
        simp [this]
    unfold hw
    rw [Finset.card_filter]
    rw [Fintype.sum_equiv e (fun i => if g (e i) c = true then 1 else 0)
      (fun x => if g x c = true then 1 else 0) (fun i => rfl)]
    rw [Fintype.sum_sum_type]
    have h1 : ∀ x : Fin r, (if g (Sum.inl x) c = true then 1 else 0) =
        if R0 c = true then 1 else 0 := fun x => rfl
    have h2 : ∀ p : Fin q × Fin b, (if g (Sum.inr p) c = true then 1 else 0) =
        if cyc p.2 c = true then 1 else 0 := fun p => rfl
    rw [Finset.sum_congr rfl (fun x _ => h1 x), Finset.sum_congr rfl (fun p _ => h2 p),
      Fintype.sum_prod_type, Finset.sum_congr rfl (fun x _ => hcnt)]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    split_ifs <;> simp

theorem majImage_hw_le {k : ℕ} {S : Set ℕ} {w : ℕ} (hw1 : 1 ≤ w) (hS : ∀ s ∈ S, s ≤ w)
    {y : Fin k → Bool} (hy : y ∈ MajImage (Ham k S)) : hw y ≤ 2 * w - 1 := by
  obtain ⟨L, hL, M, hM, rfl⟩ := hy
  have hdc : ∑ c : Fin k, hw (fun i => M i c) = ∑ i, hw (M i) := by
    unfold hw; simp only [Finset.card_filter]; exact Finset.sum_comm
  have hrow : ∑ i, hw (M i) ≤ L * w := by
    calc ∑ i, hw (M i) ≤ ∑ _i : Fin L, w := Finset.sum_le_sum (fun i _ => hS _ (hM i))
      _ = L * w := by simp
  have hlow : (L + 1) * hw (fun c => Maj L (fun l => M l c)) ≤ ∑ c : Fin k, 2 * hw (fun i => M i c) := by
    unfold hw
    rw [Finset.card_filter, Finset.mul_sum]
    refine Finset.sum_le_sum (fun c _ => ?_)
    split_ifs with h
    · simp only [Maj, decide_eq_true_eq] at h; unfold hw at h; omega
    · simp
  rw [← Finset.mul_sum, hdc] at hlow
  by_contra hcon
  push Not at hcon
  have : (L + 1) * (2 * w) ≤ 2 * (L * w) := by
    calc (L + 1) * (2 * w) ≤ (L + 1) * hw (fun c => Maj L (fun l => M l c)) :=
          Nat.mul_le_mul_left _ (by omega)
      _ ≤ 2 * ∑ i, hw (M i) := hlow
      _ ≤ 2 * (L * w) := Nat.mul_le_mul_left _ hrow
  nlinarith

theorem exists_perm_of_hw_eq {k : ℕ} (x y : Fin k → Bool) (h : hw x = hw y) :
    ∃ σ : Equiv.Perm (Fin k), y = x ∘ σ := by
  have c1 : Fintype.card {c // y c = true} = Fintype.card {c // x c = true} := by
    rw [Fintype.card_subtype, Fintype.card_subtype]; exact h.symm
  have c2 : Fintype.card {c // ¬ y c = true} = Fintype.card {c // ¬ x c = true} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, c1]
  let e1 := Fintype.equivOfCardEq c1
  let e2 := Fintype.equivOfCardEq c2
  refine ⟨e1.subtypeCongr e2, ?_⟩
  funext c
  by_cases hc : y c = true
  · rw [Function.comp_apply, Equiv.subtypeCongr, Equiv.trans_apply, Equiv.trans_apply,
      Equiv.sumCompl_symm_apply_of_pos (p := fun c => y c = true) hc]; simp only [Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl]
    rw [hc, (e1 ⟨c, hc⟩).2]
  · rw [Function.comp_apply, Equiv.subtypeCongr, Equiv.trans_apply, Equiv.trans_apply,
      Equiv.sumCompl_symm_apply_of_neg (p := fun c => y c = true) hc]; simp only [Equiv.sumCongr_apply, Sum.map_inr, Equiv.sumCompl_apply_inr]
    have := (e2 ⟨c, hc⟩).2
    simp only [Bool.not_eq_true] at hc this
    rw [hc, this]

theorem image_symm_of_ham {k L : ℕ} (f : (Fin L → Bool) → Bool) (S : Set ℕ)
    {x : Fin k → Bool} (hx : x ∈ image f (Ham k S)) (σ : Equiv.Perm (Fin k)) :
    x ∘ σ ∈ image f (Ham k S) := by
  obtain ⟨M, hM, rfl⟩ := hx
  refine ⟨fun l => M l ∘ σ, fun l => ?_, rfl⟩
  show hw _ ∈ S
  have : hw (M l ∘ σ) = hw (M l) := by
    unfold hw
    exact Finset.card_bij (fun c _ => σ c) (by simp) (fun a _ b _ h => σ.injective h)
      (fun c hc => ⟨σ.symm c, by simpa using hc, by simp⟩)
  rw [this]; exact hM l

theorem ham_subset_majImage {k : ℕ} {S : Set ℕ} {l w b : ℕ} (hl : l ∈ S) (hl1 : 1 ≤ l)
    (hwS : w ∈ S) (hwk : w ≤ k) (hlb : l ≤ b) (hbk : b ≤ k) (hbw : b ≤ 2 * w - 1) :
    Ham k {b} ⊆ MajImage (Ham k S) := by
  have hpre : (fun c : Fin k => decide (c.val < b)) ∈ MajImage (Ham k S) := by
    have hR0 : hw (fun c : Fin k => decide (c.val < w)) ∈ S := by rw [hw_prefix hwk]; exact hwS
    by_cases hwb : w ≤ b
    · have h := maj_construction (fun c : Fin k => decide (c.val < w)) hR0 1 2 w b hwS hwb hbk
        (by omega) ⟨b, by ring⟩
      convert h using 1
      funext c
      by_cases h1 : c.val < b <;> by_cases h2 : c.val < w <;> simp [h1, h2] <;> omega
    · push Not at hwb
      have h := maj_construction (fun c : Fin k => decide (c.val < w)) hR0 (2 * b - 1) 2 l b hl
        hlb hbk (by omega) ⟨2 * b - 1, by omega⟩
      convert h using 1
      funext c
      by_cases h1 : c.val < b <;> by_cases h2 : c.val < w <;> simp [h1, h2] <;> omega
  rintro y hy
  obtain ⟨σ, hσ⟩ := exists_perm_of_hw_eq _ y (by rw [hw_prefix hbk]; exact hy.symm)
  obtain ⟨L, hL, hx⟩ := hpre
  exact ⟨L, hL, hσ ▸ image_symm_of_ham _ S hx σ⟩

end Aux_majImage_ham_upper

open Aux_majImage_ham_upper in
/-- Upper half of `Maj(Ham_k(S))`: if `w = max S ≤ k` and `ℓ ∈ S` with `ℓ ≥ 1`, then every tuple in `Maj(Ham_k(S))` has weight at most `2w - 1`, and every weight `b` with `ℓ ≤ b ≤ min(k, 2w - 1)` occurs (`Ham_k({b}) ⊆ Maj(Ham_k(S))`). -/
theorem majImage_ham_upper {k : ℕ} {S : Set ℕ} {l w : ℕ} (hl : l ∈ S) (hl1 : 1 ≤ l)
    (hwS : w ∈ S) (hwk : w ≤ k) (hmax : ∀ s ∈ S, s ≤ w) :
    (∀ y ∈ MajImage (Ham k S), hw y ≤ 2 * w - 1) ∧
    (∀ b : ℕ, l ≤ b → b ≤ k → b ≤ 2 * w - 1 → Ham k {b} ⊆ MajImage (Ham k S)) := by
  have hw1 : 1 ≤ w := le_trans hl1 (hmax l hl)
  exact ⟨fun y hy => majImage_hw_le hw1 hmax hy,
    fun b hlb hbk hbw => ham_subset_majImage hl hl1 hwS hwk hlb hbk hbw⟩

end SymBoolPCSP.CFixing

open SymBoolPCSP.CFixing in
theorem solution {k : ℕ} {S : Set ℕ} {l w : ℕ} (hl : l ∈ S) (hl1 : 1 ≤ l)
    (hwS : w ∈ S) (hwk : w ≤ k) (hmax : ∀ s ∈ S, s ≤ w) :
    (∀ y ∈ MajImage (Ham k S), hw y ≤ 2 * w - 1) ∧
    (∀ b : ℕ, l ≤ b → b ≤ k → b ≤ 2 * w - 1 → Ham k {b} ⊆ MajImage (Ham k S)) :=
  SymBoolPCSP.CFixing.majImage_ham_upper hl hl1 hwS hwk hmax
