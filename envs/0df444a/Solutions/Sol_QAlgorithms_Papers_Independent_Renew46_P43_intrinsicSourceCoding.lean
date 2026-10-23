-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P43.intrinsicSourceCoding
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T22:13:38.6266+00:00
-- url     : https://prove2.me/submissions/77400132-a8f2-4210-b342-8dfce19c761a

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P43
import Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_sourceCoding

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open QAlgorithms QAlgorithms.Papers.Independent.Renew46.P43
open QAlgorithms.Papers.Independent.Claimed50.P40 (InBlocks InBlockPower)
open Filter

namespace X6ISC

variable {d n : ℕ}

/-- Kraus index: a block label for every tensor factor. -/
abbrev Lab (block : Fin d → ℕ) (n : ℕ) := Fin n → (Finset.univ.image block)

def lab (block : Fin d → ℕ) (x : Fin n → Fin d) : Lab block n :=
  fun i => ⟨block (x i), Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩

lemma lab_eq_iff (block : Fin d → ℕ) (x y : Fin n → Fin d) :
    lab block x = lab block y ↔ ∀ i, block (x i) = block (y i) := by
  constructor
  · intro h i; have := congrFun h i; simpa [lab] using this
  · intro h; funext i; simp [lab, h i]

/-- Block projector. -/
def P (block : Fin d → ℕ) (β : Lab block n) : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  Matrix.diagonal fun x => if lab block x = β then 1 else 0

def pinch (block : Fin d → ℕ) : Superop (Fin n → Fin d) (Fin n → Fin d) :=
  fun ρ => ∑ β, P block β * ρ * (P block β)ᴴ

lemma P_herm (block : Fin d → ℕ) (β : Lab block n) : (P block β)ᴴ = P block β := by
  unfold P
  rw [Matrix.diagonal_conjTranspose]
  congr 1; funext x; split_ifs <;> simp_all

lemma pinch_apply (block : Fin d → ℕ) (ρ : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) (x y) :
    pinch block ρ x y = if lab block x = lab block y then ρ x y else 0 := by
  unfold pinch
  simp only [P_herm, Matrix.sum_apply]
  simp only [P, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : lab block x = lab block y
  · rw [if_pos h]
    rw [Finset.sum_eq_single (lab block x)]
    · simp [h]
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun b _ => ?_
    by_cases hx : lab block x = b
    · have : ¬ lab block y = b := fun hy => h (hx.trans hy.symm)
      simp [this]
    · simp [hx]

lemma pinch_kraus (block : Fin d → ℕ) :
    ∑ β : Lab block n, (P block β)ᴴ * P block β = 1 := by
  ext x y
  rw [Matrix.sum_apply]
  simp only [P_herm, P, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases hxy : x = y
  · subst hxy
    simp only [if_true]
    rw [Finset.sum_eq_single (lab block x)]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  · simp [hxy]

lemma comp_channel {ι : Type} [Fintype ι]
    [DecidableEq ι] (D : Superop ι (Fin n → Fin d)) (hD : IsChannel D) (block : Fin d → ℕ) :
    IsChannel (fun ρ => pinch block (D ρ)) := by
  obtain ⟨m, E, hE, hDE⟩ := hD
  let G : Lab block n × Fin m → Matrix (Fin n → Fin d) ι ℂ := fun k => P block k.1 * E k.2
  set e := Fintype.equivFin (Lab block n × Fin m)
  refine ⟨Fintype.card (Lab block n × Fin m), fun i => G (e.symm i), ?_, fun ρ => ?_⟩
  · unfold IsKrausFamily
    rw [Equiv.sum_comp e.symm (fun k => (G k)ᴴ * G k), Fintype.sum_prod_type_right]
    have : ∀ j : Fin m, ∑ β : Lab block n, (G (β, j))ᴴ * G (β, j) = (E j)ᴴ * E j := by
      intro j
      calc _ = ∑ β : Lab block n, (E j)ᴴ * ((P block β)ᴴ * P block β) * E j := by
              simp [G, Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = (E j)ᴴ * (∑ β : Lab block n, (P block β)ᴴ * P block β) * E j := by
              rw [Matrix.mul_sum, Matrix.sum_mul]
        _ = _ := by rw [pinch_kraus, Matrix.mul_one]
    simp only [this]; exact hE
  · simp only [krausApply]
    rw [Equiv.sum_comp e.symm (fun k => G k * ρ * (G k)ᴴ), Fintype.sum_prod_type]
    unfold pinch; rw [hDE]; unfold krausApply
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [G, Matrix.conjTranspose_mul, Matrix.mul_assoc]

lemma word_off {a : ℕ} (A : IntrinsicSystem) (S : PureSource a A.dim)
    (hletters : ∀ x, InBlocks A.block (S.letter x)) (w : Fin n → Fin a) (x y : Fin n → Fin A.dim)
    (h : lab A.block x ≠ lab A.block y) : S.word w x y = 0 := by
  rw [Ne, lab_eq_iff] at h
  push Not at h
  obtain ⟨i, hi⟩ := h
  simp only [PureSource.word, wordTensor]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (hletters (w i) _ _ hi)

lemma fid_pinch {a : ℕ} (A : IntrinsicSystem) (S : PureSource a A.dim)
    (hletters : ∀ x, InBlocks A.block (S.letter x)) (w : Fin n → Fin a)
    (σ : Matrix (Fin n → Fin A.dim) (Fin n → Fin A.dim) ℂ) :
    effectProb (pinch A.block σ) (S.word w) = effectProb σ (S.word w) := by
  unfold effectProb
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, pinch_apply]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  split_ifs with h
  · rfl
  · simp [word_off A S hletters w y x (Ne.symm h)]

def pc {a : ℕ} (A : IntrinsicSystem) {S : PureSource a A.dim} (c : SourceCode S n) :
    SourceCode S n :=
  { c with
    decode := fun ρ => pinch A.block (c.decode ρ)
    decoder_channel := comp_channel c.decode c.decoder_channel A.block }

lemma pc_intrinsic {a : ℕ} (A : IntrinsicSystem) {S : PureSource a A.dim} (c : SourceCode S n) :
    IntrinsicSourceCode A (pc A c) := by
  intro T _ x y h
  show pinch A.block (c.decode T) x y = 0
  rw [pinch_apply, if_neg]
  rw [lab_eq_iff]; push Not; exact h

lemma pc_fid {a : ℕ} (A : IntrinsicSystem) {S : PureSource a A.dim}
    (hletters : ∀ x, InBlocks A.block (S.letter x)) (c : SourceCode S n) :
    (pc A c).fidelity = c.fidelity := by
  unfold SourceCode.fidelity
  refine Finset.sum_congr rfl fun w _ => ?_
  show _ * effectProb (pinch A.block (c.decode (c.encode w))) _ = _
  rw [fid_pinch A S hletters]

lemma pc_meets {a : ℕ} (A : IntrinsicSystem) {S : PureSource a A.dim}
    (hletters : ∀ x, InBlocks A.block (S.letter x)) (c : SourceCode S n) (q : Bool) (l : ℝ)
    (h : MeetsQuality c (if q then .quantumFidelity else .arbitraryFidelity) l) :
    MeetsQuality (pc A c) (if q then .quantumFidelity else .arbitraryFidelity) l := by
  cases q
  · simp only [MeetsQuality, Bool.false_eq_true, if_false] at h ⊢
    rw [pc_fid A hletters]; exact h
  · simp only [MeetsQuality, if_true] at h ⊢
    rw [pc_fid A hletters]
    exact ⟨h.1, h.2⟩

lemma rate_eq {a : ℕ} (A : IntrinsicSystem) (S : PureSource a A.dim)
    (hletters : ∀ x, InBlocks A.block (S.letter x)) (q : Bool) (l : ℝ) :
    intrinsicSourceRate A S q l =
      sourceRate S (if q then .quantumFidelity else .arbitraryFidelity) l := by
  unfold intrinsicSourceRate sourceRate minimumSourceRate
  congr 1; funext m; congr 1
  ext r
  constructor
  · rintro ⟨c, _, hc, rfl⟩; exact ⟨c, hc, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨pc A c, pc_intrinsic A c, pc_meets A hletters c q l hc, rfl⟩

end X6ISC

open X6ISC in
theorem solution {a : ℕ} (A : IntrinsicSystem) (S : PureSource a A.dim)
    (hletters : ∀ x, InBlocks A.block (S.letter x))
    (lambda : ℝ) (hlambda : 0 < lambda) (hsmall : lambda < 1) :
    intrinsicSourceRate A S true lambda = ENNReal.ofReal (vnEntropy S.average) ∧
    intrinsicSourceRate A S false lambda = ENNReal.ofReal (vnEntropy S.average) := by
  rw [rate_eq A S hletters, rate_eq A S hletters]
  have h := sourceCoding S lambda hlambda hsmall
  exact ⟨h.2.1, h.2.2⟩
