-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P28.symplectic_generator_basis
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T09:30:12.719874+00:00
-- url     : https://prove2.me/submissions/e340d8de-66f5-4e8f-a107-b5e0a0e042bb

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P28
noncomputable section
open scoped BigOperators ENNReal ComplexOrder Matrix
namespace QAlgorithms.Papers.Independent.Support50.P28
attribute [local instance] Classical.propDecidable Classical.decEq
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsTraceClassChannel rankOne)
open QAlgorithms.Papers.Independent.Claimed50.P47
  (Occupation gaussianStateCharacteristic singleCharacteristic weylKernel)
open QAlgorithms.Papers.Independent.Claimed50.P30 (phiMinus)

local notation "Gn" => sourceSymplecticGenerator

/-- coordinate functionals dual to the generators -/
def S169F_phi {n : ℕ} (a : GeneratorIndex n) (K : OscillatorCovariance (Fin n)) : ℝ :=
  match a with
  | Sum.inl (i, t) =>
      if t = 0 then (K (i,0) (i,1) - K (i,1) (i,0)) / 2
      else if t = 1 then K (i,0) (i,0) else (K (i,0) (i,1) + K (i,1) (i,0)) / 2
  | Sum.inr (p, t) =>
      if t = 0 then (K (p.1.1,0) (p.1.2,1) - K (p.1.1,1) (p.1.2,0)) / 2
      else if t = 1 then -(K (p.1.1,0) (p.1.2,0) + K (p.1.1,1) (p.1.2,1)) / 2
      else if t = 2 then (K (p.1.1,0) (p.1.2,1) + K (p.1.1,1) (p.1.2,0)) / 2
      else (K (p.1.1,0) (p.1.2,0) - K (p.1.1,1) (p.1.2,1)) / 2

def S169F_phiL {n : ℕ} (a : GeneratorIndex n) : OscillatorCovariance (Fin n) →ₗ[ℝ] ℝ where
  toFun := S169F_phi a
  map_add' x y := by
    rcases a with ⟨i, t⟩ | ⟨p, t⟩ <;> simp only [S169F_phi] <;> split_ifs <;>
      simp only [Matrix.add_apply] <;> ring
  map_smul' c x := by
    rcases a with ⟨i, t⟩ | ⟨p, t⟩ <;> simp only [S169F_phi] <;> split_ifs <;>
      simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply] <;> ring

lemma S169F_ne {n : ℕ} (p : {ij : Fin n × Fin n // ij.1 < ij.2}) : p.1.1 ≠ p.1.2 := ne_of_lt p.2

lemma S169F_dual {n : ℕ} (a b : GeneratorIndex n) :
    S169F_phi a (Gn b) = if a = b then 1 else 0 := by
  rcases a with ⟨i, t⟩ | ⟨p, t⟩ <;> rcases b with ⟨m, s⟩ | ⟨q, s⟩
  · by_cases him : i = m
    · subst him
      fin_cases t <;> fin_cases s <;>
        simp [S169F_phi, sourceSymplecticGenerator, oneModeGenerator, sourceBeta, sourceDelta]
    · simp [S169F_phi, sourceSymplecticGenerator, him]
  · have h1 := S169F_ne q
    simp only [S169F_phi, sourceSymplecticGenerator, reduceCtorEq, if_false]
    have : ¬ (i = q.1.1 ∧ i = q.1.2) := fun h => h1 (h.1.symm.trans h.2)
    have : ¬ (i = q.1.2 ∧ i = q.1.1) := fun h => h1 (h.2.symm.trans h.1)
    split_ifs <;> simp_all
  · have h1 := S169F_ne p
    simp only [S169F_phi, sourceSymplecticGenerator, reduceCtorEq, if_false]
    have : ¬ (p.1.1 = m ∧ p.1.2 = m) := fun h => h1 (h.1.trans h.2.symm)
    split_ifs <;> simp_all
  · by_cases hpq : p = q
    · subst hpq
      have h1 := S169F_ne p
      fin_cases t <;> fin_cases s <;>
        simp [S169F_phi, sourceSymplecticGenerator, sourceBeta, sourceDelta, h1, Matrix.one_apply]
    · have : ¬ (p.1.1 = q.1.1 ∧ p.1.2 = q.1.2) := fun h => hpq (Subtype.ext (Prod.ext h.1 h.2))
      have : ¬ (p.1.1 = q.1.2 ∧ p.1.2 = q.1.1) := fun h => by
        have hp := p.2; rw [h.1, h.2] at hp; exact lt_asymm hp q.2
      simp only [S169F_phi, sourceSymplecticGenerator]
      split_ifs <;> simp_all

lemma S169F_entry {n : ℕ} (K : OscillatorCovariance (Fin n)) (i j : Fin n) (α β : Fin 2) :
    (K.transpose * interleavedSigma (Fin n) + interleavedSigma (Fin n) * K) (i, α) (j, β) =
      (if β = 0 then -K (j,1) (i,α) else K (j,0) (i,α)) +
      (if α = 0 then K (i,1) (j,β) else -K (i,0) (j,β)) := by
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, interleavedSigma,
    Fintype.sum_prod_type]
  rw [Finset.sum_eq_single j, Finset.sum_eq_single i]
  · fin_cases α <;> fin_cases β <;> simp [Fin.sum_univ_two]
  · intro b _ hb; simp [Ne.symm hb]
  · simp
  · intro b _ hb; simp [hb]
  · simp

lemma S169F_sp_iff {n : ℕ} (K : OscillatorCovariance (Fin n)) : InSymplecticAlgebra K ↔
    ∀ i j, (-K (j,1) (i,0) + K (i,1) (j,0) = 0) ∧ (K (j,0) (i,0) + K (i,1) (j,1) = 0) ∧
      (-K (j,1) (i,1) - K (i,0) (j,0) = 0) ∧ (K (j,0) (i,1) - K (i,0) (j,1) = 0) := by
  unfold InSymplecticAlgebra
  constructor
  · intro h i j
    have e := fun α β => (S169F_entry K i j α β).symm.trans (congrFun (congrFun h (i, α)) (j, β))
    have e00 := e 0 0; have e01 := e 0 1; have e10 := e 1 0; have e11 := e 1 1
    simp at e00 e01 e10 e11
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  · intro h
    ext ⟨i, α⟩ ⟨j, β⟩
    rw [S169F_entry]
    obtain ⟨h1, h2, h3, h4⟩ := h i j
    fin_cases α <;> fin_cases β <;> simp <;> linarith

lemma S169F_gen_sp {n : ℕ} (b : GeneratorIndex n) : InSymplecticAlgebra (Gn b) := by
  rw [S169F_sp_iff]
  intro i j
  rcases b with ⟨m, s⟩ | ⟨p, s⟩
  · by_cases hi : i = m <;> by_cases hj : j = m
    · subst hi hj
      fin_cases s <;> simp [sourceSymplecticGenerator, oneModeGenerator, sourceBeta, sourceDelta]
    all_goals simp [sourceSymplecticGenerator, hi, hj]
  · have hp := S169F_ne p
    by_cases h1 : i = p.1.1 ∧ j = p.1.2
    · obtain ⟨rfl, rfl⟩ := h1
      fin_cases s <;> simp [sourceSymplecticGenerator, sourceBeta, sourceDelta, hp, Ne.symm hp]
    by_cases h2 : i = p.1.2 ∧ j = p.1.1
    · obtain ⟨rfl, rfl⟩ := h2
      fin_cases s <;> simp [sourceSymplecticGenerator, sourceBeta, sourceDelta, hp, Ne.symm hp]
    have h3 : ¬ (j = p.1.1 ∧ i = p.1.2) := fun h => h2 ⟨h.2, h.1⟩
    have h4 : ¬ (j = p.1.2 ∧ i = p.1.1) := fun h => h1 ⟨h.2, h.1⟩
    simp only [sourceSymplecticGenerator, if_neg h1, if_neg h2, if_neg h3, if_neg h4]
    norm_num

lemma S169F_recon {n : ℕ} (K : OscillatorCovariance (Fin n)) (hK : InSymplecticAlgebra K) :
    ∑ b, S169F_phi b K • Gn b = K := by
  rw [S169F_sp_iff] at hK
  ext ⟨i, α⟩ ⟨j, β⟩
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_prod_type]
  rcases lt_trichotomy i j with hij | rfl | hij
  · have hs : ∑ m : Fin n, ∑ s : Fin 3, S169F_phi (Sum.inl (m, s)) K *
        Gn (Sum.inl (m, s)) (i, α) (j, β) = 0 := by
      apply Finset.sum_eq_zero; intro m _; apply Finset.sum_eq_zero; intro s _
      have : ¬ (i = m ∧ j = m) := fun h => (ne_of_lt hij) (h.1.trans h.2.symm)
      simp [sourceSymplecticGenerator, this]
    rw [hs, zero_add, Finset.sum_eq_single ⟨(i, j), hij⟩]
    · obtain ⟨h1, h2, h3, h4⟩ := hK i j
      fin_cases α <;> fin_cases β <;>
        simp [Fin.sum_univ_four, S169F_phi, sourceSymplecticGenerator, sourceBeta, sourceDelta] <;> ring
    · intro p _ hp
      apply Finset.sum_eq_zero; intro s _
      have c1 : ¬ (i = p.1.1 ∧ j = p.1.2) := fun h => hp (Subtype.ext (Prod.ext h.1.symm h.2.symm))
      have c2 : ¬ (i = p.1.2 ∧ j = p.1.1) := fun h => by
        have := p.2; rw [← h.1, ← h.2] at this; exact lt_asymm this hij
      simp only [sourceSymplecticGenerator, if_neg c1, if_neg c2, mul_zero]
    · simp
  · have hp0 : ∑ p : {ij : Fin n × Fin n // ij.1 < ij.2}, ∑ s : Fin 4, S169F_phi (Sum.inr (p, s)) K *
        Gn (Sum.inr (p, s)) (i, α) (i, β) = 0 := by
      apply Finset.sum_eq_zero; intro p _; apply Finset.sum_eq_zero; intro s _
      have hp := S169F_ne p
      have c1 : ¬ (i = p.1.1 ∧ i = p.1.2) := fun h => hp (h.1.symm.trans h.2)
      have c2 : ¬ (i = p.1.2 ∧ i = p.1.1) := fun h => hp (h.2.symm.trans h.1)
      simp only [sourceSymplecticGenerator, if_neg c1, if_neg c2, mul_zero]
    rw [hp0, add_zero, Finset.sum_eq_single i]
    · obtain ⟨h1, h2, h3, h4⟩ := hK i i
      fin_cases α <;> fin_cases β <;>
        simp [Fin.sum_univ_three, S169F_phi, sourceSymplecticGenerator, oneModeGenerator,
          sourceBeta, sourceDelta] <;> linarith
    · intro m _ hm
      apply Finset.sum_eq_zero; intro s _
      simp [sourceSymplecticGenerator, Ne.symm hm]
    · simp
  · have hs : ∑ m : Fin n, ∑ s : Fin 3, S169F_phi (Sum.inl (m, s)) K *
        Gn (Sum.inl (m, s)) (i, α) (j, β) = 0 := by
      apply Finset.sum_eq_zero; intro m _; apply Finset.sum_eq_zero; intro s _
      have : ¬ (i = m ∧ j = m) := fun h => (ne_of_lt hij) (h.2.trans h.1.symm)
      simp [sourceSymplecticGenerator, this]
    rw [hs, zero_add, Finset.sum_eq_single ⟨(j, i), hij⟩]
    · obtain ⟨h1, h2, h3, h4⟩ := hK i j
      have c1 : ¬ (i = j ∧ j = i) := fun h => (ne_of_lt hij) h.2
      fin_cases α <;> fin_cases β <;>
        simp [Fin.sum_univ_four, S169F_phi, sourceSymplecticGenerator, sourceBeta, sourceDelta, c1,
          (ne_of_lt hij).symm, ne_of_lt hij] <;> linarith
    · intro p _ hp
      apply Finset.sum_eq_zero; intro s _
      have c2 : ¬ (i = p.1.2 ∧ j = p.1.1) := fun h => hp (Subtype.ext (Prod.ext h.2.symm h.1.symm))
      have c1 : ¬ (i = p.1.1 ∧ j = p.1.2) := fun h => by
        have := p.2; rw [← h.1, ← h.2] at this; exact lt_asymm this hij
      simp only [sourceSymplecticGenerator, if_neg c1, if_neg c2, mul_zero]
    · simp

def S169F_Q {n : ℕ} : GeneratorIndex n → Prop
  | Sum.inl (_, t) => t = 0
  | Sum.inr (_, t) => t = 0 ∨ t = 1

lemma S169F_compact_iff {n : ℕ} (a : GeneratorIndex n) :
    (Gn a).transpose = -Gn a ↔ S169F_Q a := by
  rcases a with ⟨i, t⟩ | ⟨p, t⟩
  · fin_cases t
    · refine iff_of_true ?_ (by simp [S169F_Q])
      ext ⟨x, α⟩ ⟨y, β⟩
      simp only [Matrix.transpose_apply, Matrix.neg_apply]
      by_cases hx : x = i <;> by_cases hy : y = i
      · subst hx hy; fin_cases α <;> fin_cases β <;> simp [sourceSymplecticGenerator, oneModeGenerator]
      all_goals simp [sourceSymplecticGenerator, hx, hy]
    · refine iff_of_false ?_ (by simp [S169F_Q])
      intro h; have := congrFun (congrFun h (i, 0)) (i, 0)
      rw [Matrix.transpose_apply, Matrix.neg_apply] at this
      simp [sourceSymplecticGenerator, oneModeGenerator, sourceBeta] at this
      norm_num at this
    · refine iff_of_false ?_ (by simp [S169F_Q])
      intro h; have := congrFun (congrFun h (i, 0)) (i, 1)
      rw [Matrix.transpose_apply, Matrix.neg_apply] at this
      simp [sourceSymplecticGenerator, oneModeGenerator, sourceDelta] at this
      norm_num at this
  · have hp := S169F_ne p
    fin_cases t
    · refine iff_of_true ?_ (by simp [S169F_Q])
      ext ⟨x, α⟩ ⟨y, β⟩
      simp only [Matrix.transpose_apply, Matrix.neg_apply]
      by_cases h1 : x = p.1.1 ∧ y = p.1.2
      · obtain ⟨rfl, rfl⟩ := h1
        fin_cases α <;> fin_cases β <;> simp [sourceSymplecticGenerator, hp, Ne.symm hp]
      by_cases h2 : x = p.1.2 ∧ y = p.1.1
      · obtain ⟨rfl, rfl⟩ := h2
        fin_cases α <;> fin_cases β <;> simp [sourceSymplecticGenerator, hp, Ne.symm hp]
      have h3 : ¬ (y = p.1.1 ∧ x = p.1.2) := fun h => h2 ⟨h.2, h.1⟩
      have h4 : ¬ (y = p.1.2 ∧ x = p.1.1) := fun h => h1 ⟨h.2, h.1⟩
      simp only [sourceSymplecticGenerator, if_neg h1, if_neg h2, if_neg h3, if_neg h4, neg_zero]
    · refine iff_of_true ?_ (by simp [S169F_Q])
      ext ⟨x, α⟩ ⟨y, β⟩
      simp only [Matrix.transpose_apply, Matrix.neg_apply]
      by_cases h1 : x = p.1.1 ∧ y = p.1.2
      · obtain ⟨rfl, rfl⟩ := h1
        fin_cases α <;> fin_cases β <;> simp [sourceSymplecticGenerator, hp, Ne.symm hp]
      by_cases h2 : x = p.1.2 ∧ y = p.1.1
      · obtain ⟨rfl, rfl⟩ := h2
        fin_cases α <;> fin_cases β <;> simp [sourceSymplecticGenerator, hp, Ne.symm hp]
      have h3 : ¬ (y = p.1.1 ∧ x = p.1.2) := fun h => h2 ⟨h.2, h.1⟩
      have h4 : ¬ (y = p.1.2 ∧ x = p.1.1) := fun h => h1 ⟨h.2, h.1⟩
      simp only [sourceSymplecticGenerator, if_neg h1, if_neg h2, if_neg h3, if_neg h4, neg_zero]
    · refine iff_of_false ?_ (by simp [S169F_Q])
      intro h; have := congrFun (congrFun h (p.1.1, 0)) (p.1.2, 1)
      rw [Matrix.transpose_apply, Matrix.neg_apply] at this
      simp [sourceSymplecticGenerator, sourceDelta, hp, Ne.symm hp] at this
      norm_num at this
    · refine iff_of_false ?_ (by simp [S169F_Q])
      intro h; have := congrFun (congrFun h (p.1.1, 0)) (p.1.2, 0)
      rw [Matrix.transpose_apply, Matrix.neg_apply] at this
      simp [sourceSymplecticGenerator, sourceBeta, hp, Ne.symm hp] at this
      norm_num at this

lemma S169F_phi_noncompact {n : ℕ} (K : OscillatorCovariance (Fin n)) (hK : InSymplecticAlgebra K)
    (hs : K.transpose = -K) (a : GeneratorIndex n) (ha : ¬ S169F_Q a) : S169F_phi a K = 0 := by
  rw [S169F_sp_iff] at hK
  have sk : ∀ u v, K v u = -K u v := fun u v => by
    have := congrFun (congrFun hs u) v; simpa using this
  rcases a with ⟨i, t⟩ | ⟨p, t⟩
  · fin_cases t
    · exact absurd rfl ha
    · simp [S169F_phi]; have := sk (i,0) (i,0); linarith
    · simp [S169F_phi]; have := sk (i,0) (i,1); linarith
  · fin_cases t
    · exact absurd (Or.inl rfl) ha
    · exact absurd (Or.inr rfl) ha
    · simp [S169F_phi]
      have h4 := (hK p.1.2 p.1.1).2.2.2
      have := sk (p.1.2, 0) (p.1.1, 1)
      linarith
    · simp [S169F_phi]
      have h2 := (hK p.1.1 p.1.2).2.1
      have := sk (p.1.2, 0) (p.1.1, 0)
      linarith

lemma S169F_card_lt (n : ℕ) :
    2 * Fintype.card {ij : Fin n × Fin n // ij.1 < ij.2} + n = n ^ 2 := by
  have hgt : Fintype.card {ij : Fin n × Fin n // ij.2 < ij.1} =
      Fintype.card {ij : Fin n × Fin n // ij.1 < ij.2} :=
    Fintype.card_congr
      { toFun := fun p => ⟨p.1.swap, p.2⟩, invFun := fun p => ⟨p.1.swap, p.2⟩,
        left_inv := fun p => rfl, right_inv := fun p => rfl }
  have heq : Fintype.card {ij : Fin n × Fin n // ij.1 = ij.2} = n := by
    rw [Fintype.card_congr (Equiv.ofBijective (fun i : Fin n => (⟨(i, i), rfl⟩ :
      {ij : Fin n × Fin n // ij.1 = ij.2})) ⟨fun a b h => by
        simpa using congrArg (fun p => p.1.1) h, fun p => ⟨p.1.1, by
          ext <;> simp [p.2]⟩⟩).symm]
    simp
  have hsum : ∀ p : Fin n × Fin n, ((if p.1 < p.2 then 1 else 0) + (if p.1 = p.2 then 1 else 0) +
      (if p.2 < p.1 then 1 else 0) : ℕ) = 1 := by
    intro p
    rcases lt_trichotomy p.1 p.2 with h | h | h
    · simp [h, ne_of_lt h, not_lt_of_gt h]
    · simp [h]
    · simp [h, (ne_of_lt h).symm, not_lt_of_gt h]
  have htot : Fintype.card {ij : Fin n × Fin n // ij.1 < ij.2} +
      Fintype.card {ij : Fin n × Fin n // ij.1 = ij.2} +
      Fintype.card {ij : Fin n × Fin n // ij.2 < ij.1} = n ^ 2 := by
    simp only [Fintype.card_subtype, Finset.card_filter]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.sum_congr rfl (fun p _ => hsum p)]
    simp [sq]
  omega

lemma S169F_card_gen (n : ℕ) : Fintype.card (GeneratorIndex n) = 2 * n ^ 2 + n := by
  have := S169F_card_lt n
  simp only [GeneratorIndex, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  nlinarith

lemma S169F_card_compact (n : ℕ) : Fintype.card (CompactGeneratorIndex n) = n ^ 2 := by
  have := S169F_card_lt n
  rw [Fintype.card_congr (Equiv.subtypeEquivRight S169F_compact_iff),
    Fintype.card_subtype, Finset.card_filter]
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_prod_type, S169F_Q, Fin.sum_univ_three, Fin.sum_univ_four]
  simp
  omega

def S169F_spSub (n : ℕ) : Submodule ℝ (OscillatorCovariance (Fin n)) where
  carrier := {K | InSymplecticAlgebra K}
  zero_mem' := by simp [InSymplecticAlgebra]
  add_mem' {A B} hA hB := by
    simp only [Set.mem_setOf_eq, InSymplecticAlgebra] at *
    rw [Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add]
    rw [show Aᵀ * interleavedSigma (Fin n) + Bᵀ * interleavedSigma (Fin n) +
      (interleavedSigma (Fin n) * A + interleavedSigma (Fin n) * B) =
      (Aᵀ * interleavedSigma (Fin n) + interleavedSigma (Fin n) * A) +
      (Bᵀ * interleavedSigma (Fin n) + interleavedSigma (Fin n) * B) by abel, hA, hB, add_zero]
  smul_mem' c A hA := by
    simp only [Set.mem_setOf_eq, InSymplecticAlgebra] at *
    rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hA, smul_zero]

def S169F_spSkew (n : ℕ) : Submodule ℝ (OscillatorCovariance (Fin n)) where
  carrier := {K | InSymplecticAlgebra K ∧ K.transpose = -K}
  zero_mem' := ⟨(S169F_spSub n).zero_mem, by simp⟩
  add_mem' {A B} hA hB := ⟨(S169F_spSub n).add_mem hA.1 hB.1, by
    rw [Matrix.transpose_add, hA.2, hB.2, neg_add]⟩
  smul_mem' c A hA := ⟨(S169F_spSub n).smul_mem c hA.1, by
    rw [Matrix.transpose_smul, hA.2, smul_neg]⟩

theorem S169F_main (n : ℕ) (hn : 0 < n) :
    LinearIndependent ℝ (sourceSymplecticGenerator (n := n)) ∧
    (↑(Submodule.span ℝ (Set.range (sourceSymplecticGenerator (n := n)))) : Set (OscillatorCovariance (Fin n))) =
      {K | InSymplecticAlgebra K} ∧
    Fintype.card (GeneratorIndex n) = 2 * n ^ 2 + n ∧
    LinearIndependent ℝ (fun a : CompactGeneratorIndex n => sourceSymplecticGenerator a.val) ∧
    (↑(Submodule.span ℝ (Set.range (fun a : CompactGeneratorIndex n => sourceSymplecticGenerator a.val))) :
      Set (OscillatorCovariance (Fin n))) = {K | InSymplecticAlgebra K ∧ K.transpose = -K} ∧
    Fintype.card (CompactGeneratorIndex n) = n ^ 2 := by
  have hli : LinearIndependent ℝ (sourceSymplecticGenerator (n := n)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg b
    have := congrArg (S169F_phiL b) hg
    simp only [map_sum, map_smul, map_zero] at this
    simp only [S169F_phiL, LinearMap.coe_mk, AddHom.coe_mk, S169F_dual, smul_eq_mul, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at this
    exact this
  refine ⟨hli, ?_, S169F_card_gen n, hli.comp _ Subtype.val_injective, ?_, S169F_card_compact n⟩
  · ext K
    constructor
    · intro hK
      have : Submodule.span ℝ (Set.range (sourceSymplecticGenerator (n := n))) ≤ S169F_spSub n := by
        rw [Submodule.span_le]; rintro _ ⟨b, rfl⟩; exact S169F_gen_sp b
      exact this hK
    · intro hK
      rw [SetLike.mem_coe, ← S169F_recon K hK]
      exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
  · ext K
    constructor
    · intro hK
      have : Submodule.span ℝ (Set.range (fun a : CompactGeneratorIndex n => sourceSymplecticGenerator a.val))
          ≤ S169F_spSkew n := by
        rw [Submodule.span_le]; rintro _ ⟨b, rfl⟩; exact ⟨S169F_gen_sp b.val, b.2⟩
      exact this hK
    · rintro ⟨hK, hs⟩
      rw [SetLike.mem_coe, ← S169F_recon K hK,
        ← Fintype.sum_subtype_add_sum_subtype (fun b => (Gn b).transpose = -Gn b)]
      have hz : ∑ b : {b // ¬ (Gn b).transpose = -Gn b}, S169F_phi b.val K • Gn b.val = 0 := by
        apply Finset.sum_eq_zero; intro b _
        rw [S169F_phi_noncompact K hK hs b.val (fun h => b.2 ((S169F_compact_iff _).mpr h)), zero_smul]
      rw [hz, add_zero]
      exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
end QAlgorithms.Papers.Independent.Support50.P28

end

open QAlgorithms.Papers.Independent.Support50.P28 in
theorem solution (n : ℕ) (hn : 0 < n) :
    LinearIndependent ℝ (sourceSymplecticGenerator (n := n)) ∧
    (↑(Submodule.span ℝ (Set.range (sourceSymplecticGenerator (n := n)))) : Set (OscillatorCovariance (Fin n))) =
      {K | InSymplecticAlgebra K} ∧
    Fintype.card (GeneratorIndex n) = 2 * n ^ 2 + n ∧
    LinearIndependent ℝ (fun a : CompactGeneratorIndex n => sourceSymplecticGenerator a.val) ∧
    (↑(Submodule.span ℝ (Set.range (fun a : CompactGeneratorIndex n => sourceSymplecticGenerator a.val))) :
      Set (OscillatorCovariance (Fin n))) = {K | InSymplecticAlgebra K ∧ K.transpose = -K} ∧
    Fintype.card (CompactGeneratorIndex n) = n ^ 2 :=
  S169F_main n hn
