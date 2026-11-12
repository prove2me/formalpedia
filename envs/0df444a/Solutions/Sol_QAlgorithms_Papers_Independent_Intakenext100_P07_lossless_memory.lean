-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P07.lossless_memory
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-12T01:06:42.432986+00:00
-- url     : https://prove2.me/submissions/5bd5ae23-eb71-4094-aabe-1cec632c669f

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P07

noncomputable section

open Filter

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J A B C D X Y Z : Type*}
variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]
variable [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
variable [Fintype Z] [DecidableEq Z]

open QAlgorithms.Papers.Independent.Intakenext100.P07 in
theorem solution [Nonempty X] (p : X → ℝ) (hp : paperProbability p) :
    let k := Nat.ceil (Real.logb 2 ((Finset.univ.filter (fun x => 0 < p x)).card:ℝ))
    (∃ c : paperSourceCode X (2^k), ∀ x, 0 < p x → c.decode (c.encode x) = x) ∧
    ∀ m : ℕ, (∃ c : paperSourceCode X (2^m), ∀ x, 0 < p x → c.decode (c.encode x) = x) → k ≤ m := by
  intro k
  obtain ⟨S, hS⟩ : ∃ S : Finset X, S = Finset.univ.filter (fun x => 0 < p x) := ⟨_, rfl⟩
  have hk : k = Nat.ceil (Real.logb 2 (S.card : ℝ)) := by rw [hS]
  clear_value k
  have hmem : ∀ x, x ∈ S ↔ 0 < p x := by
    intro x; rw [hS]; simp
  have hSpos : 0 < S.card := by
    rw [Finset.card_pos]
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have hle : ∀ x, p x ≤ 0 := by
      intro x
      by_contra hx
      push_neg at hx
      have hx' := (hmem x).2 hx
      rw [hne] at hx'
      simp at hx'
    have hsum : ∑ x, p x ≤ 0 := Finset.sum_nonpos (fun x _ => hle x)
    have h1 := hp.2
    linarith
  have hSpos' : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast hSpos
  have hlog : ∀ m : ℕ, S.card ≤ 2 ^ m → k ≤ m := by
    intro m hm
    rw [hk]
    apply Nat.ceil_le.mpr
    rw [Real.logb_le_iff_le_rpow (show (1:ℝ) < 2 by norm_num) hSpos', Real.rpow_natCast]
    exact_mod_cast hm
  have hk2 : S.card ≤ 2 ^ k := by
    have h1 : Real.logb 2 (S.card : ℝ) ≤ (k : ℝ) := by
      rw [hk]; exact Nat.le_ceil _
    rw [Real.logb_le_iff_le_rpow (show (1:ℝ) < 2 by norm_num) hSpos', Real.rpow_natCast] at h1
    exact_mod_cast h1
  refine ⟨?_, ?_⟩
  · have h2k : 0 < 2 ^ k := by positivity
    refine ⟨⟨fun x => if hx : x ∈ S then Fin.castLE hk2 (S.equivFin ⟨x, hx⟩) else ⟨0, h2k⟩,
            fun y => if hy : y.val < S.card then (S.equivFin.symm ⟨y.val, hy⟩).val
              else Classical.arbitrary X⟩, ?_⟩
    intro x hx
    have hxS : x ∈ S := (hmem x).2 hx
    dsimp only
    rw [dif_pos hxS]
    have hlt : (Fin.castLE hk2 (S.equivFin ⟨x, hxS⟩)).val < S.card := (S.equivFin ⟨x, hxS⟩).isLt
    rw [dif_pos hlt]
    have he : (⟨(Fin.castLE hk2 (S.equivFin ⟨x, hxS⟩)).val, hlt⟩ : Fin S.card) =
        S.equivFin ⟨x, hxS⟩ := Fin.ext rfl
    rw [he, Equiv.symm_apply_apply]
  · rintro m ⟨c, hc⟩
    apply hlog m
    have hcard := Finset.card_le_card_of_injOn c.encode (s := S) (t := Finset.univ)
      (by intro a _; exact Finset.mem_univ _)
      (by
        intro a ha b hb hab
        have ha' := hc a ((hmem a).1 ha)
        have hb' := hc b ((hmem b).1 hb)
        calc a = c.decode (c.encode a) := ha'.symm
          _ = c.decode (c.encode b) := by rw [hab]
          _ = b := hb')
    rw [Finset.card_univ, Fintype.card_fin] at hcard
    exact hcard

end
