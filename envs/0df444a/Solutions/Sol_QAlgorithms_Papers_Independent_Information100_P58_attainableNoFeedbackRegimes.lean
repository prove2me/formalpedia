-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P58.attainableNoFeedbackRegimes
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T05:21:27.196291+00:00
-- url     : https://prove2.me/submissions/16dc5c9f-ad08-4cfd-ab17-c421472152f7

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P58

open scoped BigOperators

namespace G54W
open QAlgorithms.Papers.Independent.Information100.P58

/-- restriction of a code to a pattern -/
def res {n d M : ℕ} (C : Fin M → Word n d) (S : Finset (Fin n)) (m : Fin M) :
    {i : Fin n // i ∈ S} → Fin d := fun i => C m i.val

lemma compat_eq {n d M : ℕ} (C : Fin M → Word n d) (S : Finset (Fin n)) (m : Fin M) :
    compatible C S m = Finset.univ.filter (fun j => res C S j = res C S m) := by
  ext j
  simp only [compatible, Finset.mem_filter, Finset.mem_univ, true_and, res, funext_iff, Subtype.forall]

lemma fiber_sum {M : ℕ} {β : Type*} [DecidableEq β] (g : Fin M → β) :
    ∑ m, (1 : ℝ) / ((Finset.univ.filter (fun j => g j = g m)).card : ℝ) =
      ((Finset.univ.image g).card : ℝ) := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image g) (g := g)
    (fun m _ => Finset.mem_image_of_mem g (Finset.mem_univ m))]
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_congr rfl fun b hb => ?_
  obtain ⟨m0, -, rfl⟩ := Finset.mem_image.mp hb
  have : ∀ m ∈ Finset.univ.filter (fun m => g m = g m0),
      (1 : ℝ) / ((Finset.univ.filter (fun j => g j = g m)).card : ℝ) =
        1 / ((Finset.univ.filter (fun j => g j = g m0)).card : ℝ) := by
    intro m hm
    rw [(Finset.mem_filter.mp hm).2]
  rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
  have hpos : (0 : ℝ) < ((Finset.univ.filter (fun j => g j = g m0)).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨m0, by simp⟩
  field_simp
  simp

lemma avg_eq {n d M : ℕ} (p : ℝ) (C : Fin M → Word n d) :
    deterministicAverage p C =
      ∑ S : Finset (Fin n), patternWeight n p S * ((Finset.univ.image (res C S)).card : ℝ) / M := by
  unfold deterministicAverage deterministicIndividual
  have hc : ∑ m : Fin M, ∑ S : Finset (Fin n), patternWeight n p S / ((compatible C S m).card : ℝ) =
      ∑ S : Finset (Fin n), ∑ m : Fin M, patternWeight n p S / ((compatible C S m).card : ℝ) :=
    Finset.sum_comm
  rw [hc, Finset.sum_div]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [← fiber_sum (res C S)]
  simp only [Finset.mul_sum, Finset.sum_div, compat_eq]
  refine Finset.sum_congr rfl fun m _ => by ring

lemma dim_eq (n d : ℕ) (p : ℝ) (M : ℝ) :
    dimensionSuccess n d p M =
      ∑ S : Finset (Fin n), patternWeight n p S * min 1 ((d : ℝ) ^ S.card / M) := by
  unfold dimensionSuccess patternWeight binomialWeight
  rw [← Finset.powerset_univ]
  rw [Finset.sum_powerset_apply_card (fun k => (1 - p) ^ k * p ^ (n - k) * min 1 ((d : ℝ) ^ k / M))]
  rw [Finset.card_univ, Fintype.card_fin]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [nsmul_eq_mul]; ring

lemma card_res_le {n d M : ℕ} (C : Fin M → Word n d) (S : Finset (Fin n)) :
    Fintype.card ({i : Fin n // i ∈ S} → Fin d) = d ^ S.card := by
  simp [Fintype.card_fun, Fintype.card_coe]

lemma term_inj {M k d : ℕ} (hM : 0 < M) (h : M ≤ d ^ k) :
    (M : ℝ) / M = min 1 ((d : ℝ) ^ k / M) := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  rw [div_self hM'.ne', eq_comm, min_eq_left]
  rw [le_div_iff₀ hM', one_mul]; exact_mod_cast h

lemma term_surj {M k d : ℕ} (hM : 0 < M) (h : d ^ k ≤ M) :
    ((d ^ k : ℕ) : ℝ) / M = min 1 ((d : ℝ) ^ k / M) := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  push_cast
  rw [eq_comm, min_eq_right]
  rw [div_le_iff₀ hM', one_mul]; exact_mod_cast h

lemma card_inj {n d M : ℕ} {C : Fin M → Word n d} {S : Finset (Fin n)}
    (h : Function.Injective (res C S)) : (Finset.univ.image (res C S)).card = M := by
  rw [Finset.card_image_of_injective _ h, Finset.card_univ, Fintype.card_fin]

lemma card_surj {n d M : ℕ} {C : Fin M → Word n d} {S : Finset (Fin n)}
    (h : Function.Surjective (res C S)) : (Finset.univ.image (res C S)).card = d ^ S.card := by
  rw [Finset.image_univ_of_surjective h, Finset.card_univ, card_res_le C S]

lemma main_eq {n d M : ℕ} (hM : 0 < M) (p : ℝ) (C : Fin M → Word n d)
    (h : ∀ S : Finset (Fin n), ((Finset.univ.image (res C S)).card : ℝ) / M =
      min 1 ((d : ℝ) ^ S.card / M)) :
    deterministicAverage p C = dimensionSuccess n d p M := by
  rw [avg_eq, dim_eq]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [mul_div_assoc, h S]

lemma surj_of_surj {n d M : ℕ} (hd : 0 < d) {C : Fin M → Word n d} (hC : Function.Surjective C)
    (S : Finset (Fin n)) : Function.Surjective (res C S) := by
  intro f
  obtain ⟨m, hm⟩ := hC (fun i => if h : i ∈ S then f ⟨i, h⟩ else ⟨0, hd⟩)
  refine ⟨m, funext fun i => ?_⟩
  simp [res, hm, i.2]

end G54W

open QAlgorithms.Papers.Independent.Information100.P58

theorem solution (n d M : ℕ) (hn : 0<n) (hd : 2≤d) (hM : 0<M)
    (p : ℝ) (hp0 : 0≤p) (hp1 : p≤1) :
    (M≤d → ∃ C : Fin M → Word n d, Function.Injective C ∧ (∀ m i j, C m i = C m j) ∧
      deterministicAverage p C = dimensionSuccess n d p M) ∧
    (d^n≤M → (∃ C : Fin M → Word n d, Function.Surjective C ∧
      deterministicAverage p C = dimensionSuccess n d p M) ∧
      ∀ C : Fin M → Word n d, Function.Surjective C →
      deterministicAverage p C = dimensionSuccess n d p M) ∧
    (∀ r : ℕ, r≤n → M=d^r → ∀ C : Fin M → Word n d,
      (∀ S : Finset (Fin n), S.card=r →
        Function.Bijective (fun m => fun i : {i : Fin n // i∈S} => C m i.val)) →
      deterministicAverage p C = dimensionSuccess n d p M ∧
      (∀ S : Finset (Fin n), S.card≤r → Function.Surjective
        (fun m => fun i : {i : Fin n // i∈S} => C m i.val)) ∧
      (∀ S : Finset (Fin n), r≤S.card → Function.Injective
        (fun m => fun i : {i : Fin n // i∈S} => C m i.val))) := by
  have hd0 : 0 < d := by omega
  refine ⟨fun hMd => ?_, fun hdn => ?_, fun r hr hMr C hbij => ?_⟩
  · -- repetition code
    let C : Fin M → Word n d := fun m _ => ⟨m.val, lt_of_lt_of_le m.2 hMd⟩
    refine ⟨C, ?_, fun m i j => rfl, ?_⟩
    · intro m m' h
      have := congrFun h ⟨0, hn⟩
      simp only [C, Fin.mk.injEq] at this
      exact Fin.ext this
    · apply G54W.main_eq hM
      intro S
      rcases S.eq_empty_or_nonempty with hS | ⟨i0, hi0⟩
      · subst hS
        have hc : (Finset.univ.image (G54W.res C ∅)).card = 1 := by
          rw [Finset.card_eq_one]
          refine ⟨G54W.res C ∅ ⟨0, hM⟩, ?_⟩
          ext f
          simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_singleton]
          constructor
          · rintro ⟨m, rfl⟩; funext i; exact absurd i.2 (Finset.notMem_empty _)
          · rintro rfl; exact ⟨⟨0, hM⟩, rfl⟩
        rw [hc]
        have := G54W.term_surj (d := d) (k := 0) hM (by simpa using Nat.one_le_iff_ne_zero.mpr hM.ne')
        simpa using this
      · have hinj : Function.Injective (G54W.res C S) := by
          intro m m' h
          have := congrFun h ⟨i0, hi0⟩
          simp only [G54W.res, C, Fin.mk.injEq] at this
          exact Fin.ext this
        rw [G54W.card_inj hinj]
        apply G54W.term_inj hM
        have hk : S.card ≠ 0 := (Finset.card_pos.mpr ⟨i0, hi0⟩).ne'
        calc M ≤ d := hMd
          _ ≤ d ^ S.card := Nat.le_self_pow hk d
  · have hsurj_main : ∀ C : Fin M → Word n d, Function.Surjective C →
        deterministicAverage p C = dimensionSuccess n d p M := by
      intro C hC
      apply G54W.main_eq hM
      intro S
      rw [G54W.card_surj (G54W.surj_of_surj hd0 hC S)]
      apply G54W.term_surj hM
      calc d ^ S.card ≤ d ^ n := by
            apply Nat.pow_le_pow_right hd0
            simpa using Finset.card_le_univ S
        _ ≤ M := hdn
    refine ⟨?_, hsurj_main⟩
    have hcard : Fintype.card (Word n d) = d ^ n := by simp [Fintype.card_fun]
    let e : Word n d ≃ Fin (d ^ n) := Fintype.equivFinOfCardEq hcard
    have hpos : 0 < d ^ n := Nat.pow_pos hd0
    let C : Fin M → Word n d := fun m =>
      if h : m.val < d ^ n then e.symm ⟨m.val, h⟩ else e.symm ⟨0, hpos⟩
    have hC : Function.Surjective C := by
      intro w
      refine ⟨⟨(e w).val, lt_of_lt_of_le (e w).2 hdn⟩, ?_⟩
      simp only [C, (e w).2, dite_true]
      simp
    exact ⟨C, hC, hsurj_main C hC⟩
  · -- MDS case
    have hsurj : ∀ S : Finset (Fin n), S.card ≤ r → Function.Surjective (G54W.res C S) := by
      intro S hS f
      obtain ⟨T, hST, -, hT⟩ := Finset.exists_subsuperset_card_eq (Finset.subset_univ S) hS
        (by simpa using hr)
      obtain ⟨m, hm⟩ := (hbij T hT).2 (fun i => if h : i.val ∈ S then f ⟨i.val, h⟩ else ⟨0, hd0⟩)
      refine ⟨m, funext fun i => ?_⟩
      have := congrFun hm ⟨i.val, hST i.2⟩
      simp only [i.2, dite_true] at this
      exact this
    have hinj : ∀ S : Finset (Fin n), r ≤ S.card → Function.Injective (G54W.res C S) := by
      intro S hS m m' h
      obtain ⟨T, hTS, hT⟩ := Finset.exists_subset_card_eq hS
      apply (hbij T hT).1
      funext i
      exact congrFun h ⟨i.val, hTS i.2⟩
    refine ⟨?_, hsurj, hinj⟩
    apply G54W.main_eq hM
    intro S
    rcases le_total S.card r with h | h
    · rw [G54W.card_surj (hsurj S h)]
      apply G54W.term_surj hM
      rw [hMr]; exact Nat.pow_le_pow_right hd0 h
    · rw [G54W.card_inj (hinj S h)]
      apply G54W.term_inj hM
      rw [hMr]; exact Nat.pow_le_pow_right hd0 h
