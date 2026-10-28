-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P16.weylCovariance_iff_positiveDefinite
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T22:36:27.148639+00:00
-- url     : https://prove2.me/submissions/3934610a-1421-4fa8-b1e0-76a43cf06116

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P16

-- ===== WYA =====

noncomputable section

namespace X4WY

open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms.Papers.Independent.Gap20.P16
open QAlgorithms.Papers.Independent.Information100.P26 (Mat Unitary)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {H : Type*} [AddCommGroup H]

lemma cv_add_left (b b' : CharacterGroup H) (a : H) :
    characterValue (b + b') a = characterValue b a * characterValue b' a := by
  simp [characterValue]

lemma cv_add_right (b : CharacterGroup H) (a a' : H) :
    characterValue b (a + a') = characterValue b a * characterValue b a' := by
  simp [characterValue, AddChar.map_add_eq_mul]

lemma cv_zero_left (a : H) : characterValue (0 : CharacterGroup H) a = 1 := by
  simp [characterValue]

lemma cv_zero_right (b : CharacterGroup H) : characterValue b (0 : H) = 1 := by
  simp [characterValue]

lemma cv_norm (b : CharacterGroup H) (a : H) : ‖characterValue b a‖ = 1 :=
  Circle.norm_coe _

lemma cv_conj_mul (b : CharacterGroup H) (a : H) :
    conj (characterValue b a) * characterValue b a = 1 := by
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, cv_norm]; simp

lemma cv_mul_conj (b : CharacterGroup H) (a : H) :
    characterValue b a * conj (characterValue b a) = 1 := by
  rw [mul_comm, cv_conj_mul]

lemma cv_neg_left (b : CharacterGroup H) (a : H) :
    characterValue (-b) a = conj (characterValue b a) := by
  have h := cv_add_left (-b) b a
  rw [neg_add_cancel, cv_zero_left] at h
  have h2 := cv_conj_mul b a
  calc characterValue (-b) a = characterValue (-b) a * (characterValue b a * conj (characterValue b a)) := by
        rw [cv_mul_conj, mul_one]
    _ = conj (characterValue b a) := by rw [← mul_assoc, ← h, one_mul]

lemma cv_neg_right (b : CharacterGroup H) (a : H) :
    characterValue b (-a) = conj (characterValue b a) := by
  have h := cv_add_right b (-a) a
  rw [neg_add_cancel, cv_zero_right] at h
  calc characterValue b (-a) = characterValue b (-a) * (characterValue b a * conj (characterValue b a)) := by
        rw [cv_mul_conj, mul_one]
    _ = conj (characterValue b a) := by rw [← mul_assoc, ← h, one_mul]

lemma cv_sub_right (b : CharacterGroup H) (a a' : H) :
    characterValue b (a - a') = characterValue b a * conj (characterValue b a') := by
  rw [sub_eq_add_neg, cv_add_right, cv_neg_right]

lemma cv_sub_left (b b' : CharacterGroup H) (a : H) :
    characterValue (b - b') a = characterValue b a * conj (characterValue b' a) := by
  rw [sub_eq_add_neg, cv_add_left, cv_neg_left]

/-- Nontrivial characters exist. -/
lemma exists_cv_ne_one [Finite H] {a : H} (ha : a ≠ 0) :
    ∃ b : CharacterGroup H, characterValue b a ≠ 1 := by
  obtain ⟨ψ, hψ⟩ := (AddChar.exists_apply_ne_zero (a := a)).2 ha
  refine ⟨Additive.ofMul (AddChar.circleEquivComplex.symm ψ), ?_⟩
  have : ((AddChar.circleEquivComplex.symm ψ) a : ℂ) = ψ a := rfl
  simpa [characterValue, this] using hψ

lemma exists_cv_ne_one' {b : CharacterGroup H} (hb : b ≠ 0) :
    ∃ a : H, characterValue b a ≠ 1 := by
  by_contra h
  push Not at h
  apply hb
  change Additive.ofMul (Additive.toMul b) = Additive.ofMul 1
  congr 1
  ext a
  have := h a
  simp only [characterValue] at this
  simpa using this

variable {d : ℕ}

/-- shorthand for a Weyl operator as a matrix -/
abbrev Wm (W : FiniteAbelianWeylSystem H d) (z : H × CharacterGroup H) : Matrix (Fin d) (Fin d) ℂ :=
  (finiteAbelianWeylOperator W z : Mat d)

lemma Wm_def (W : FiniteAbelianWeylSystem H d) (z : H × CharacterGroup H) :
    Wm W z = (W.U z.1 : Mat d) * (W.V z.2 : Mat d) := by
  simp [Wm, finiteAbelianWeylOperator]

lemma Wm_star_mul (W : FiniteAbelianWeylSystem H d) (z) : (Wm W z)ᴴ * Wm W z = 1 :=
  Matrix.mem_unitaryGroup_iff'.1 (finiteAbelianWeylOperator W z).2

lemma Wm_mul_star (W : FiniteAbelianWeylSystem H d) (z) : Wm W z * (Wm W z)ᴴ = 1 :=
  Matrix.mem_unitaryGroup_iff.1 (finiteAbelianWeylOperator W z).2

lemma U_add' (W : FiniteAbelianWeylSystem H d) (a a' : H) :
    (W.U (a + a') : Mat d) = (W.U a : Mat d) * (W.U a' : Mat d) := by
  rw [W.U_add]; rfl

lemma V_add' (W : FiniteAbelianWeylSystem H d) (b b' : CharacterGroup H) :
    (W.V (b + b') : Mat d) = (W.V b : Mat d) * (W.V b' : Mat d) := by
  rw [W.V_add]; rfl

/-- product law -/
lemma Wm_mul (W : FiniteAbelianWeylSystem H d) (z w : H × CharacterGroup H) :
    Wm W z * Wm W w = characterValue z.2 w.1 • Wm W (z + w) := by
  rw [Wm_def, Wm_def, Wm_def, Prod.fst_add, Prod.snd_add, U_add', V_add']
  calc (W.U z.1 : Mat d) * (W.V z.2 : Mat d) * ((W.U w.1 : Mat d) * (W.V w.2 : Mat d))
      = (W.U z.1 : Mat d) * ((W.V z.2 : Mat d) * (W.U w.1 : Mat d)) * (W.V w.2 : Mat d) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [W.commutation]
        simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

lemma Wm_zero (W : FiniteAbelianWeylSystem H d) : Wm W 0 = 1 := by
  simp [Wm_def, W.U_zero, W.V_zero]

/-- commutation phase: `W zᴴ W w W z = pair z w • W w` -/
def pair (z w : H × CharacterGroup H) : ℂ :=
  characterValue w.2 z.1 * conj (characterValue z.2 w.1)

lemma pair_norm (z w : H × CharacterGroup H) : ‖pair z w‖ = 1 := by
  simp [pair, cv_norm]

lemma pair_conj_mul (z w : H × CharacterGroup H) : conj (pair z w) * pair z w = 1 := by
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, pair_norm]; simp

lemma pair_mul_conj (z w : H × CharacterGroup H) : pair z w * conj (pair z w) = 1 := by
  rw [mul_comm, pair_conj_mul]

lemma pair_add_left (z z' w : H × CharacterGroup H) :
    pair (z + z') w = pair z w * pair z' w := by
  simp only [pair, Prod.fst_add, Prod.snd_add, cv_add_left, cv_add_right, map_mul]; ring

lemma pair_add_right (z w w' : H × CharacterGroup H) :
    pair z (w + w') = pair z w * pair z w' := by
  simp only [pair, Prod.fst_add, Prod.snd_add, cv_add_left, cv_add_right, map_mul]; ring

lemma pair_zero_left (w : H × CharacterGroup H) : pair 0 w = 1 := by
  simp [pair, cv_zero_left, cv_zero_right]

lemma pair_zero_right (z : H × CharacterGroup H) : pair z 0 = 1 := by
  simp [pair, cv_zero_left, cv_zero_right]

lemma pair_sub_right (z w w' : H × CharacterGroup H) :
    pair z (w - w') = pair z w * conj (pair z w') := by
  have h := pair_add_right z (w - w') w'
  rw [sub_add_cancel] at h
  calc pair z (w - w') = pair z (w - w') * (pair z w' * conj (pair z w')) := by
        rw [pair_mul_conj, mul_one]
    _ = pair z w * conj (pair z w') := by rw [← mul_assoc, ← h]

lemma Wm_conj (W : FiniteAbelianWeylSystem H d) (z w : H × CharacterGroup H) :
    (Wm W z)ᴴ * Wm W w * Wm W z = pair z w • Wm W w := by
  have h1 := Wm_mul W w z
  have h2 := Wm_mul W z w
  rw [add_comm] at h1
  -- W w W z = cv w.2 z.1 • W(z+w), W z W w = cv z.2 w.1 • W (z+w)
  have h3 : Wm W w * Wm W z = (characterValue w.2 z.1 * conj (characterValue z.2 w.1)) •
      (Wm W z * Wm W w) := by
    rw [h1, h2, smul_smul, mul_assoc, cv_conj_mul, mul_one]
  rw [Matrix.mul_assoc, h3, Matrix.mul_smul, ← Matrix.mul_assoc, Wm_star_mul, Matrix.one_mul]
  rfl

lemma Wm_conj' (W : FiniteAbelianWeylSystem H d) (z w : H × CharacterGroup H) :
    Wm W z * Wm W w * (Wm W z)ᴴ = conj (pair z w) • Wm W w := by
  have h := Wm_conj W z w
  have : Wm W w = pair z w • (Wm W z * Wm W w * (Wm W z)ᴴ) := by
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← h]
    simp only [Matrix.mul_assoc, Wm_mul_star, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Wm_mul_star, Matrix.one_mul]
  conv_rhs => rw [this, smul_smul, pair_conj_mul, one_smul]

/-- `W zᴴ W s = pair z s • W s W zᴴ` -/
lemma Wm_star_comm (W : FiniteAbelianWeylSystem H d) (z s : H × CharacterGroup H) :
    (Wm W z)ᴴ * Wm W s = pair z s • (Wm W s * (Wm W z)ᴴ) := by
  have h := Wm_conj W z s
  calc (Wm W z)ᴴ * Wm W s = (Wm W z)ᴴ * Wm W s * Wm W z * (Wm W z)ᴴ := by
        rw [Matrix.mul_assoc _ (Wm W z), Wm_mul_star, Matrix.mul_one]
    _ = _ := by rw [h, Matrix.smul_mul]

variable [Fintype H] [Fintype (CharacterGroup H)]

lemma exists_pair_ne_one {w : H × CharacterGroup H} (hw : w ≠ 0) :
    ∃ z, pair z w ≠ 1 := by
  by_cases h2 : w.2 = 0
  · have h1 : w.1 ≠ 0 := by
      intro h1; apply hw; ext <;> simp [h1, h2]
    obtain ⟨b, hb⟩ := exists_cv_ne_one h1
    refine ⟨(0, b), ?_⟩
    simp only [pair, cv_zero_right, one_mul]
    intro h; apply hb
    have := congrArg conj h
    simpa using this
  · obtain ⟨a, ha⟩ := exists_cv_ne_one' h2
    refine ⟨(a, 0), ?_⟩
    simpa [pair, cv_zero_left] using ha

lemma sum_pair_eq_zero {w : H × CharacterGroup H} (hw : w ≠ 0) :
    ∑ z, pair z w = 0 := by
  obtain ⟨z0, hz0⟩ := exists_pair_ne_one hw
  have h : ∑ z, pair z w = pair z0 w * ∑ z, pair z w := by
    rw [Finset.mul_sum]
    simp_rw [← pair_add_left]
    exact (Fintype.sum_equiv (Equiv.addLeft z0) _ _ (fun _ => rfl)).symm
  have : (1 - pair z0 w) * ∑ z, pair z w = 0 := by rw [sub_mul, one_mul, ← h, sub_self]
  rcases mul_eq_zero.1 this with h1 | h1
  · exact absurd (sub_eq_zero.1 h1).symm hz0
  · exact h1

/-- orthogonality of the commutation phases -/
lemma sum_pair_orth (w w' : H × CharacterGroup H) :
    ∑ z, pair z w * conj (pair z w') =
      if w = w' then (Fintype.card (H × CharacterGroup H) : ℂ) else 0 := by
  simp_rw [← pair_sub_right]
  split_ifs with h
  · subst h; simp [pair_zero_right]
  · exact sum_pair_eq_zero (sub_ne_zero.2 h)

lemma trace_Wm (W : FiniteAbelianWeylSystem H d) {w : H × CharacterGroup H} (hw : w ≠ 0) :
    (Wm W w).trace = 0 := by
  obtain ⟨z, hz⟩ := exists_pair_ne_one hw
  have h := congrArg Matrix.trace (Wm_conj W z w)
  rw [Matrix.trace_mul_cycle, Wm_mul_star, Matrix.one_mul, Matrix.trace_smul, smul_eq_mul] at h
  have : (1 - pair z w) * (Wm W w).trace = 0 := by rw [sub_mul, one_mul, ← h, sub_self]
  rcases mul_eq_zero.1 this with h1 | h1
  · exact absurd (sub_eq_zero.1 h1).symm hz
  · exact h1

lemma Wm_star_mul_eq (W : FiniteAbelianWeylSystem H d) (z w : H × CharacterGroup H) :
    (Wm W z)ᴴ * Wm W w = conj (characterValue z.2 (w - z).1) • Wm W (w - z) := by
  have h := Wm_mul W z (w - z)
  rw [add_sub_cancel] at h
  have h2 := congrArg (fun M => (Wm W z)ᴴ * M) h
  simp only [← Matrix.mul_assoc, Wm_star_mul, Matrix.one_mul, Matrix.mul_smul] at h2
  rw [h2, smul_smul, cv_conj_mul, one_smul]

lemma trace_star_mul (W : FiniteAbelianWeylSystem H d) (z w : H × CharacterGroup H) :
    ((Wm W z)ᴴ * Wm W w).trace = if z = w then (d : ℂ) else 0 := by
  split_ifs with h
  · subst h; rw [Wm_star_mul]; simp
  · rw [Wm_star_mul_eq, Matrix.trace_smul, trace_Wm W (sub_ne_zero.2 (Ne.symm h)), smul_zero]

end X4WY

-- ===== WYB =====

noncomputable section

namespace X4WY

open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms.Papers.Independent.Gap20.P16
open QAlgorithms.Papers.Independent.Information100.P26 (Mat Unitary)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Schur's lemma for the matrix-level irreducibility predicate. -/
lemma schur {G : Type*} {d : ℕ} (hd : 0 < d) (ρ : G → Mat d)
    (hirr : QAlgorithms.Papers.Independent.Support21.P09.Irreducible ρ)
    (T : Mat d) (hT : ∀ g, ρ g * T = T * ρ g) : ∃ c : ℂ, T = c • 1 := by
  haveI : Nontrivial (Fin d → ℂ) := by
    haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    infer_instance
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (Matrix.toLin' T)
  set S := Module.End.eigenspace (Matrix.toLin' T) μ
  have hinv : ∀ g v, v ∈ S → (ρ g).mulVec v ∈ S := by
    intro g v hv
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    simp only [Matrix.toLin'_apply] at hv ⊢
    rw [Matrix.mulVec_mulVec, ← hT, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]
  rcases hirr.2 S hinv with h | h
  · exact absurd h hμ
  · refine ⟨μ, ?_⟩
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    have hv : v ∈ S := by rw [h]; trivial
    rw [Module.End.mem_eigenspace_iff] at hv
    rw [hv]
    simp [Matrix.toLin'_apply, Matrix.smul_mulVec, Matrix.one_mulVec]

variable {H : Type*} [AddCommGroup H] [Fintype H] [Fintype (CharacterGroup H)] {d : ℕ}

local notation "GG" => H × CharacterGroup H

/-- twirl -/
def tw (W : FiniteAbelianWeylSystem H d) (X : Mat d) : Mat d :=
  ∑ s : GG, Wm W s * X * (Wm W s)ᴴ

lemma Wm_mul_ad (W : FiniteAbelianWeylSystem H d) (z s : GG) (X : Mat d) :
    Wm W z * (Wm W s * X * (Wm W s)ᴴ) * (Wm W z)ᴴ = Wm W (z + s) * X * (Wm W (z + s))ᴴ := by
  have h := Wm_mul W z s
  calc Wm W z * (Wm W s * X * (Wm W s)ᴴ) * (Wm W z)ᴴ
      = (Wm W z * Wm W s) * X * (Wm W z * Wm W s)ᴴ := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [h, Matrix.conjTranspose_smul]
        simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
        rw [show star (characterValue z.2 s.1) * characterValue z.2 s.1 = 1 from cv_conj_mul _ _,
          one_smul]

lemma tw_comm (W : FiniteAbelianWeylSystem H d) (X : Mat d) (z : GG) :
    Wm W z * tw W X = tw W X * Wm W z := by
  have h : Wm W z * tw W X * (Wm W z)ᴴ = tw W X := by
    simp only [tw, Matrix.mul_sum, Matrix.sum_mul]
    simp_rw [Wm_mul_ad]
    exact Fintype.sum_equiv (Equiv.addLeft z) _ _ (fun _ => rfl)
  calc Wm W z * tw W X = Wm W z * tw W X * (Wm W z)ᴴ * Wm W z := by
        rw [Matrix.mul_assoc _ _ (Wm W z), Wm_star_mul, Matrix.mul_one]
    _ = _ := by rw [h]

lemma trace_tw (W : FiniteAbelianWeylSystem H d) (X : Mat d) :
    (tw W X).trace = (Fintype.card GG : ℂ) * X.trace := by
  simp only [tw, Matrix.trace_sum]
  simp_rw [Matrix.trace_mul_cycle (Wm W _) X, Wm_star_mul, Matrix.one_mul]
  simp

lemma tw_eq (hd : 0 < d) (W : FiniteAbelianWeylSystem H d)
    (hirr : QAlgorithms.Papers.Independent.Support21.P09.Irreducible (fun z => Wm W z))
    (X : Mat d) : tw W X = ((Fintype.card GG : ℂ) * X.trace / d) • 1 := by
  obtain ⟨c, hc⟩ := schur hd _ hirr (tw W X) (fun z => tw_comm W X z)
  have ht := trace_tw W X
  rw [hc, Matrix.trace_smul, Matrix.trace_one] at ht
  simp only [Fintype.card_fin, smul_eq_mul] at ht
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [hc]; congr 1
  field_simp
  rw [← ht]

end X4WY

-- ===== WYC =====

noncomputable section

namespace X4WY

open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms.Papers.Independent.Gap20.P16
open QAlgorithms.Papers.Independent.Information100.P26 (Mat Unitary)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {H : Type*} [AddCommGroup H] [Fintype H] [Fintype (CharacterGroup H)] {d : ℕ}

local notation "GG" => H × CharacterGroup H

lemma tw_entry (hd : 0 < d) (W : FiniteAbelianWeylSystem H d)
    (hirr : QAlgorithms.Papers.Independent.Support21.P09.Irreducible (fun z => Wm W z)) (a c i k : Fin d) :
    ∑ z : GG, Wm W z a c * star (Wm W z k i) =
      if a = k ∧ c = i then (Fintype.card GG : ℂ) / d else 0 := by
  have h := congrFun (congrFun (tw_eq hd W hirr (Matrix.single c i 1)) a) k
  simp only [tw, Matrix.sum_apply, Matrix.mul_apply, Matrix.single_apply,
    Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.one_apply, ite_and, mul_ite, ite_mul,
    mul_one, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Matrix.trace, Matrix.diag] at h
  rw [h]
  by_cases hci : c = i
  · subst hci; by_cases hak : a = k <;> simp [hak, Fintype.card_prod]
  · simp [hci, Ne.symm hci]

/-- operator-basis expansion (unnormalized) -/
lemma expand0 (hd : 0 < d) (W : FiniteAbelianWeylSystem H d)
    (hirr : QAlgorithms.Papers.Independent.Support21.P09.Irreducible (fun z => Wm W z))
    (X : Matrix (Fin d) (Fin d) ℂ) :
    ∑ z : GG, ((Wm W z)ᴴ * X).trace • Wm W z = ((Fintype.card GG : ℂ) / d) • X := by
  ext a c
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Matrix.conjTranspose_apply]
  calc ∑ z : GG, (∑ i, ∑ k, star (Wm W z k i) * X k i) * Wm W z a c
      = ∑ i, ∑ k, X k i * ∑ z : GG, Wm W z a c * star (Wm W z k i) := by
        simp_rw [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro i _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro k _
        apply Finset.sum_congr rfl; intro z _
        ring
    _ = _ := by
        simp_rw [tw_entry hd W hirr, ite_and, mul_ite, mul_zero]
        simp [Finset.sum_ite_eq, Finset.sum_ite_eq', mul_comm]

lemma Wm_ne_zero (hd : 0 < d) (W : FiniteAbelianWeylSystem H d) (z : GG) : Wm W z ≠ 0 := by
  intro h
  have h1 := Wm_star_mul W z
  rw [h, Matrix.mul_zero] at h1
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  exact zero_ne_one (α := Matrix (Fin d) (Fin d) ℂ) h1

lemma card_eq (hd : 0 < d) (W : FiniteAbelianWeylSystem H d)
    (hirr : QAlgorithms.Papers.Independent.Support21.P09.Irreducible (fun z => Wm W z)) :
    (Fintype.card GG : ℂ) = (d : ℂ) ^ 2 := by
  have h := expand0 hd W hirr (Wm W 0)
  simp_rw [trace_star_mul, ite_smul, zero_smul] at h
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hW := Wm_ne_zero hd W 0
  have : ((d : ℂ) - Fintype.card GG / d) • Wm W 0 = 0 := by rw [sub_smul, h, sub_self]
  rcases smul_eq_zero.1 this with h1 | h1
  · rw [sub_eq_zero] at h1; field_simp at h1; rw [h1]
  · exact absurd h1 hW

/-- normalized expansion `X = (1/d) Σ tr(W zᴴ X) W z` -/
lemma expand (hd : 0 < d) (W : FiniteAbelianWeylSystem H d)
    (hirr : QAlgorithms.Papers.Independent.Support21.P09.Irreducible (fun z => Wm W z))
    (X : Matrix (Fin d) (Fin d) ℂ) : X = ∑ z : GG, (((Wm W z)ᴴ * X).trace / d) • Wm W z := by
  have h := expand0 hd W hirr X
  rw [card_eq hd W hirr] at h
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have e : ∑ z : GG, (((Wm W z)ᴴ * X).trace / d) • Wm W z =
      (d : ℂ)⁻¹ • ∑ z : GG, ((Wm W z)ᴴ * X).trace • Wm W z := by
    rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro z _; rw [smul_smul, div_eq_inv_mul]
  rw [e, h, smul_smul, show (d : ℂ)⁻¹ * ((d : ℂ) ^ 2 / d) = 1 by field_simp, one_smul]

end X4WY

-- ===== WYD =====

noncomputable section

namespace X4WY

open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms.Papers.Independent.Gap20.P16
open QAlgorithms.Papers.Independent.Information100.P26 (Mat Unitary)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {H : Type*} [AddCommGroup H] [Fintype H] [Fintype (CharacterGroup H)] {d : ℕ}

local notation "GG" => H × CharacterGroup H

lemma sum_sandwich {ι : Type*} [Fintype ι] (c c' : ι → ℂ) (M M' : ι → Matrix (Fin d) (Fin d) ℂ)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    (∑ z, c z • M z) * X * (∑ z, c' z • M' z)ᴴ =
      ∑ z, ∑ z', (c z * conj (c' z')) • (M z * X * (M' z')ᴴ) := by
  rw [Matrix.conjTranspose_sum, Matrix.sum_mul, Matrix.sum_mul]
  apply Finset.sum_congr rfl; intro z _
  rw [Matrix.mul_sum]
  apply Finset.sum_congr rfl; intro z' _
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rfl

/-- coefficient of `E` along `W z` -/
def kap (W : FiniteAbelianWeylSystem H d) (E : Matrix (Fin d) (Fin d) ℂ) (z : GG) : ℂ :=
  ((Wm W z)ᴴ * E).trace / d

lemma conj_E (hd : 0 < d) (W : FiniteAbelianWeylSystem H d)
    (hirr : QAlgorithms.Papers.Independent.Support21.P09.Irreducible (fun z => Wm W z))
    (E : Matrix (Fin d) (Fin d) ℂ) (s : GG) :
    (Wm W s)ᴴ * E * Wm W s = ∑ z : GG, (kap W E z * pair s z) • Wm W z := by
  conv_lhs => rw [expand hd W hirr E]
  rw [Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl; intro z _
  rw [Matrix.mul_smul, Matrix.smul_mul, Wm_conj, smul_smul]
  rfl

lemma twirl_kraus (hd : 0 < d) (W : FiniteAbelianWeylSystem H d)
    (hirr : QAlgorithms.Papers.Independent.Support21.P09.Irreducible (fun z => Wm W z))
    (E X : Matrix (Fin d) (Fin d) ℂ) :
    ∑ s : GG, ((Wm W s)ᴴ * E * Wm W s) * X * ((Wm W s)ᴴ * E * Wm W s)ᴴ =
      (Fintype.card GG : ℂ) • ∑ z : GG, (kap W E z * conj (kap W E z)) • (Wm W z * X * (Wm W z)ᴴ) := by
  simp_rw [conj_E hd W hirr E, sum_sandwich]
  rw [Finset.sum_comm]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl; intro z _
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  have : ∀ z' : GG, ∑ s : GG, kap W E z * pair s z * conj (kap W E z' * pair s z') =
      kap W E z * conj (kap W E z') * (if z = z' then (Fintype.card GG : ℂ) else 0) := by
    intro z'
    rw [← sum_pair_orth z z', Finset.mul_sum]
    apply Finset.sum_congr rfl; intro s _
    rw [map_mul]; ring
  simp_rw [this, mul_ite, mul_zero, ite_smul, zero_smul]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true, smul_smul]
  congr 1; ring

lemma kap_normSq (W : FiniteAbelianWeylSystem H d) (E : Matrix (Fin d) (Fin d) ℂ) (z : GG) :
    kap W E z * conj (kap W E z) = (Complex.normSq (kap W E z) : ℂ) := by
  rw [Complex.mul_conj]

/-- random-unitary (Weyl-diagonal) form of a covariant channel -/
theorem fwd (hd : 0 < d) (W : FiniteAbelianWeylSystem H d)
    (hirr : QAlgorithms.Papers.Independent.Support21.P09.Irreducible (fun z => Wm W z))
    (Phi : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ)
    (m : ℕ) (E : Fin m → Matrix (Fin d) (Fin d) ℂ) (hK : ∑ j, (E j)ᴴ * E j = 1)
    (hPhi : ∀ X, Phi X = ∑ j, E j * X * (E j)ᴴ)
    (hcov : ∀ z X, Phi ((Wm W z)ᴴ * X * Wm W z) = (Wm W z)ᴴ * Phi X * Wm W z) :
    ∃ r : GG → ℝ, (∀ z, 0 ≤ r z) ∧ ∑ z, r z = 1 ∧
      ∀ X, Phi X = ∑ z, (r z : ℂ) • (Wm W z * X * (Wm W z)ᴴ) := by
  set r : GG → ℝ := fun z => ∑ j, Complex.normSq (kap W (E j) z) with hr
  have hG : (Fintype.card GG : ℂ) ≠ 0 := by
    have : 0 < Fintype.card GG := Fintype.card_pos
    exact_mod_cast this.ne'
  have main : ∀ X, Phi X = ∑ z, (r z : ℂ) • (Wm W z * X * (Wm W z)ᴴ) := by
    intro X
    have h1 : ∀ s : GG, Phi X = (Wm W s)ᴴ * Phi (Wm W s * X * (Wm W s)ᴴ) * Wm W s := by
      intro s
      rw [← hcov]
      congr 1
      simp only [← Matrix.mul_assoc, Wm_star_mul, Matrix.one_mul]
      rw [Matrix.mul_assoc, Wm_star_mul, Matrix.mul_one]
    have h2 : (Fintype.card GG : ℂ) • Phi X =
        ∑ j, ∑ s : GG, ((Wm W s)ᴴ * E j * Wm W s) * X * ((Wm W s)ᴴ * E j * Wm W s)ᴴ := by
      rw [Finset.sum_comm]
      have : (Fintype.card GG : ℂ) • Phi X = ∑ s : GG, Phi X := by
        rw [Finset.sum_const, Finset.card_univ]; norm_cast
      rw [this]
      apply Finset.sum_congr rfl; intro s _
      rw [h1 s, hPhi, Matrix.mul_sum, Matrix.sum_mul]
      apply Finset.sum_congr rfl; intro j _
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    simp_rw [twirl_kraus hd W hirr, kap_normSq] at h2
    rw [← Finset.smul_sum] at h2
    have h3 := congrArg (fun M => (Fintype.card GG : ℂ)⁻¹ • M) h2
    simp only [smul_smul, inv_mul_cancel₀ hG, one_smul] at h3
    rw [h3, Finset.sum_comm]
    apply Finset.sum_congr rfl; intro z _
    rw [← Finset.sum_smul, hr]
    push_cast
    rfl
  refine ⟨r, fun z => Finset.sum_nonneg (fun j _ => Complex.normSq_nonneg _), ?_, main⟩
  -- trace preservation
  have h1 := main 1
  simp only [Matrix.mul_one, Wm_mul_star] at h1
  rw [← Finset.sum_smul] at h1
  have h2 : (Phi 1).trace = d := by
    rw [hPhi]
    simp only [Matrix.mul_one, Matrix.trace_sum]
    simp_rw [Matrix.trace_mul_comm (E _) ((E _)ᴴ)]
    rw [← Matrix.trace_sum, hK, Matrix.trace_one, Fintype.card_fin]
  rw [h1, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul] at h2
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have : (∑ z, (r z : ℂ)) = 1 := by
    have := mul_right_cancel₀ hd' (h2.trans (one_mul _).symm)
    exact this
  exact_mod_cast this

end X4WY

-- ===== WYE =====

noncomputable section

namespace X4WY

open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms QAlgorithms.Papers.Independent.Gap20.P16
open QAlgorithms.Papers.Independent.Information100.P26 (Mat Unitary)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {H : Type*} [AddCommGroup H] [Fintype H] [Fintype (CharacterGroup H)] {d : ℕ}

local notation "GG" => H × CharacterGroup H

/-- `t ↦ (-t.2, t.1)` -/
def jeq : CharacterGroup H × H ≃ H × CharacterGroup H :=
  (Equiv.prodComm _ _).trans (Equiv.prodCongr (Equiv.neg H) (Equiv.refl _))

@[simp] lemma jeq_apply (t : CharacterGroup H × H) : jeq t = (-t.2, t.1) := rfl

lemma fm_eq (W : FiniteAbelianWeylSystem H d) (p : CharacterGroup H × H → ℝ) (X : Mat d) :
    fourierMixture W p X = ∑ t, (p t : ℂ) • (Wm W (jeq t) * X * (Wm W (jeq t))ᴴ) := rfl

lemma fm_eq' (W : FiniteAbelianWeylSystem H d) (p : CharacterGroup H × H → ℝ) (X : Mat d) :
    fourierMixture W p X = ∑ z : GG, (p (jeq.symm z) : ℂ) • (Wm W z * X * (Wm W z)ᴴ) := by
  rw [fm_eq]
  exact Fintype.sum_equiv jeq _ _ (fun t => by rw [Equiv.symm_apply_apply])

lemma conj_pair_j (t : CharacterGroup H × H) (w : GG) :
    conj (pair (jeq t) w) = characterValue t.1 w.1 * characterValue w.2 t.2 := by
  simp only [jeq_apply, pair, map_mul, Complex.conj_conj, cv_neg_right]
  ring

lemma fm_W (W : FiniteAbelianWeylSystem H d) (p : CharacterGroup H × H → ℝ) (w : GG) :
    fourierMixture W p (Wm W w) = fourierCharacteristic p w • Wm W w := by
  rw [fm_eq, fourierCharacteristic, Finset.sum_smul]
  apply Finset.sum_congr rfl; intro t _
  rw [Wm_conj', smul_smul, conj_pair_j, mul_assoc]

lemma fm_add (W : FiniteAbelianWeylSystem H d) (p : CharacterGroup H × H → ℝ) (X Y : Mat d) :
    fourierMixture W p (X + Y) = fourierMixture W p X + fourierMixture W p Y := by
  simp only [fm_eq, ← Finset.sum_add_distrib, Matrix.mul_add, Matrix.add_mul, smul_add]

lemma fm_smul (W : FiniteAbelianWeylSystem H d) (p : CharacterGroup H × H → ℝ) (c : ℂ) (X : Mat d) :
    fourierMixture W p (c • X) = c • fourierMixture W p X := by
  simp only [fm_eq, Finset.smul_sum, Matrix.mul_smul, Matrix.smul_mul, smul_comm c]

lemma fm_sum (W : FiniteAbelianWeylSystem H d) (p : CharacterGroup H × H → ℝ)
    {ι : Type*} (s : Finset ι) (c : ι → ℂ) (X : ι → Mat d) :
    fourierMixture W p (∑ i ∈ s, c i • X i) = ∑ i ∈ s, c i • fourierMixture W p (X i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have := fm_smul W p 0 0
    simpa using this
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, fm_add, fm_smul, ih]

lemma fm_cov (W : FiniteAbelianWeylSystem H d) (p : CharacterGroup H × H → ℝ) :
    WeylCovariant W (fourierMixture W p) := by
  intro z X
  change fourierMixture W p ((Wm W z)ᴴ * X * Wm W z) = (Wm W z)ᴴ * fourierMixture W p X * Wm W z
  rw [fm_eq, fm_eq, Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl; intro t _
  rw [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  set s := jeq t
  have h1 := Wm_star_comm W z s
  have h2 : (Wm W s)ᴴ * Wm W z = conj (pair z s) • (Wm W z * (Wm W s)ᴴ) := by
    have := congrArg Matrix.conjTranspose h1
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_smul] at this
    exact this
  calc Wm W s * ((Wm W z)ᴴ * X * Wm W z) * (Wm W s)ᴴ
      = (Wm W s * (Wm W z)ᴴ) * X * (Wm W z * (Wm W s)ᴴ) := by simp only [Matrix.mul_assoc]
    _ = (Wm W z)ᴴ * (Wm W s * X * (Wm W s)ᴴ) * Wm W z := by
      have e1 : Wm W s * (Wm W z)ᴴ = conj (pair z s) • ((Wm W z)ᴴ * Wm W s) := by
        rw [h1, smul_smul, pair_conj_mul, one_smul]
      have e2 : Wm W z * (Wm W s)ᴴ = pair z s • ((Wm W s)ᴴ * Wm W z) := by
        rw [h2, smul_smul, pair_mul_conj, one_smul]
      rw [e1, e2, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, pair_conj_mul,
        one_smul]
      simp only [Matrix.mul_assoc]

lemma fm_channel (W : FiniteAbelianWeylSystem H d) (p : CharacterGroup H × H → ℝ)
    (hp : ∀ t, 0 ≤ p t) (hs : ∑ t, p t = 1) : IsChannel (fourierMixture W p) := by
  set e := Fintype.equivFin (CharacterGroup H × H)
  refine ⟨Fintype.card (CharacterGroup H × H),
    fun k => ((Real.sqrt (p (e.symm k)) : ℝ) : ℂ) • Wm W (jeq (e.symm k)), ?_, ?_⟩
  · unfold IsKrausFamily
    have : ∀ t, ((((Real.sqrt (p t) : ℝ) : ℂ) • Wm W (jeq t))ᴴ *
        (((Real.sqrt (p t) : ℝ) : ℂ) • Wm W (jeq t))) = (p t : ℂ) • (1 : Mat d) := by
      intro t
      rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Wm_star_mul]
      congr 1
      rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (hp t)]
    rw [Fintype.sum_equiv e.symm _ (fun t => (p t : ℂ) • (1 : Mat d)) (fun k => this _)]
    rw [← Finset.sum_smul, ← Complex.ofReal_sum, hs, Complex.ofReal_one, one_smul]
  · intro ρ
    rw [fm_eq, krausApply]
    refine (Fintype.sum_equiv e.symm _ _ (fun k => ?_)).symm
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    congr 1
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (hp _)]

end X4WY

-- ===== WYF =====

noncomputable section

namespace X4WY

open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms QAlgorithms.Papers.Independent.Gap20.P16
open QAlgorithms.Papers.Independent.Information100.P26 (Mat Unitary)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {H : Type*} [AddCommGroup H] [Fintype H] [Fintype (CharacterGroup H)]

local notation "GG" => H × CharacterGroup H

/-- dual pairing -/
def chi (t : CharacterGroup H × H) (w : GG) : ℂ :=
  characterValue t.1 w.1 * characterValue w.2 t.2

lemma chi_eq (t : CharacterGroup H × H) (w : GG) : chi t w = conj (pair (jeq t) w) :=
  (conj_pair_j t w).symm

lemma chi_sub (t : CharacterGroup H × H) (w w' : GG) :
    chi t (w - w') = chi t w * conj (chi t w') := by
  simp only [chi_eq, pair_sub_right, map_mul, Complex.conj_conj]

lemma chi_zero (t : CharacterGroup H × H) : chi t 0 = 1 := by
  simp [chi, cv_zero_left, cv_zero_right]

lemma orth_t (w w' : GG) :
    ∑ t : CharacterGroup H × H, chi t w * conj (chi t w') =
      if w = w' then (Fintype.card GG : ℂ) else 0 := by
  have h := sum_pair_orth (H := H) w w'
  have h2 := congrArg conj h
  rw [map_sum] at h2
  have e : ∑ t : CharacterGroup H × H, chi t w * conj (chi t w') =
      ∑ s : GG, conj (pair s w * conj (pair s w')) := by
    refine Fintype.sum_equiv jeq _ _ (fun t => ?_)
    simp only [chi_eq, map_mul, Complex.conj_conj]
  rw [e, h2]
  split_ifs <;> simp

lemma fc_eq (p : CharacterGroup H × H → ℝ) (w : GG) :
    fourierCharacteristic p w = ∑ t, (p t : ℂ) * chi t w := by
  simp only [fourierCharacteristic, chi, mul_assoc]

lemma fc_zero (p : CharacterGroup H × H → ℝ) :
    fourierCharacteristic p 0 = ((∑ t, p t : ℝ) : ℂ) := by
  simp [fc_eq, chi_zero]

lemma fc_pd (p : CharacterGroup H × H → ℝ) (hp : ∀ t, 0 ≤ p t) :
    PositiveDefinite (fourierCharacteristic p) := by
  intro n z
  have e : (fun i j : Fin n => fourierCharacteristic p (z i - z j)) =
      ∑ t, (p t : ℂ) • Matrix.vecMulVec (fun i => chi t (z i)) (star fun i => chi t (z i)) := by
    ext i j
    simp only [fc_eq, chi_sub, Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
      Pi.star_apply, smul_eq_mul]
    rfl
  rw [e]
  refine Matrix.posSemidef_sum _ (fun t _ => ?_)
  exact (Matrix.posSemidef_vecMulVec_self_star _).smul (by exact_mod_cast hp t)

/-- finite Bochner theorem -/
lemma bochner (phi : GG → ℂ) (h0 : phi 0 = 1) (hpd : PositiveDefinite phi) :
    ∃ p : CharacterGroup H × H → ℝ, (∀ t, 0 ≤ p t) ∧ ∑ t, p t = 1 ∧
      ∀ w, fourierCharacteristic p w = phi w := by
  set N : ℂ := (Fintype.card GG : ℂ) with hN
  have hNpos : (0 : ℝ) < Fintype.card GG := by exact_mod_cast Fintype.card_pos
  have hN0 : N ≠ 0 := by rw [hN]; exact_mod_cast hNpos.ne'
  set q : CharacterGroup H × H → ℂ := fun t => N⁻¹ * ∑ w, phi w * conj (chi t w) with hq
  -- positivity
  have hq0 : ∀ t, 0 ≤ q t := by
    intro t
    set e := Fintype.equivFin GG
    have h := (hpd (Fintype.card GG) e.symm).dotProduct_mulVec_nonneg (fun i => chi t (e.symm i))
    have hval : star (fun i => chi t (e.symm i)) ⬝ᵥ
        ((fun i j : Fin (Fintype.card GG) => phi (e.symm i - e.symm j)) *ᵥ
          (fun i => chi t (e.symm i))) = N * N * q t := by
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
      have s1 : ∀ u v : GG, star (chi t u) * (phi (u - v) * chi t v) =
          phi (u - v) * conj (chi t (u - v)) := by
        intro u v; rw [chi_sub, map_mul, Complex.conj_conj, Complex.star_def]; ring
      have s2 : ∑ i : Fin (Fintype.card GG), ∑ j : Fin (Fintype.card GG),
          star (chi t (e.symm i)) * (phi (e.symm i - e.symm j) * chi t (e.symm j)) =
          ∑ u : GG, ∑ v : GG, phi (u - v) * conj (chi t (u - v)) := by
        refine Fintype.sum_equiv e.symm _ _ (fun i => ?_)
        exact Fintype.sum_equiv e.symm _ _ (fun j => s1 _ _)
      rw [s2, Finset.sum_comm]
      have s3 : ∀ v : GG, ∑ u : GG, phi (u - v) * conj (chi t (u - v)) =
          ∑ w : GG, phi w * conj (chi t w) := by
        intro v
        exact Fintype.sum_equiv (Equiv.subRight v) _ _ (fun _ => rfl)
      simp_rw [s3]
      rw [Finset.sum_const, Finset.card_univ, hq, nsmul_eq_mul, ← hN]
      field_simp
    rw [hval] at h
    have e2 : q t = ((((Fintype.card GG : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) * (N * N * q t) := by
      rw [hN]; push_cast; field_simp
    rw [e2]
    refine mul_nonneg ?_ h
    have : (0 : ℝ) ≤ ((Fintype.card GG : ℝ) ^ 2)⁻¹ := by positivity
    exact_mod_cast this
  have hqr : ∀ t, ((q t).re : ℂ) = q t := by
    intro t
    have := hq0 t
    rw [Complex.nonneg_iff] at this
    apply Complex.ext <;> simp [this.2.symm]
  -- inversion
  have hinv : ∀ w, ∑ t, q t * chi t w = phi w := by
    intro w
    simp only [hq, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    have : ∀ w' : GG, ∑ t : CharacterGroup H × H, N⁻¹ * (phi w' * conj (chi t w')) * chi t w =
        N⁻¹ * phi w' * (if w = w' then N else 0) := by
      intro w'
      rw [← orth_t w w', Finset.mul_sum]
      apply Finset.sum_congr rfl; intro t _; ring
    simp_rw [this, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true]
    field_simp
  refine ⟨fun t => (q t).re, fun t => (Complex.nonneg_iff.1 (hq0 t)).1, ?_, ?_⟩
  · have h := hinv 0
    simp only [chi_zero, mul_one, h0] at h
    have : (((∑ t, (q t).re : ℝ)) : ℂ) = 1 := by
      push_cast; simp_rw [hqr]; exact h
    exact_mod_cast this
  · intro w
    rw [fc_eq]
    simp_rw [hqr]
    exact hinv w

end X4WY

-- ===== WYSol2 =====

open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms QAlgorithms.Papers.Independent.Gap20.P16
open QAlgorithms.Papers.Independent.Information100.P26 (Mat Unitary)

section
attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution
    {d : ℕ} (hd : 0 < d) {H : Type*} [AddCommGroup H] [Fintype H]
    [Fintype (CharacterGroup H)]
    (W : FiniteAbelianWeylSystem H d) (hirr : QAlgorithms.Papers.Independent.Support21.P09.Irreducible (fun z => (finiteAbelianWeylOperator W z : Mat d)))
    (Phi : Mat d →ₗ[ℂ] Mat d) :
    ((IsChannel Phi ∧ WeylCovariant W Phi) ↔
      ∃ phi : H × CharacterGroup H → ℂ, phi 0 = 1 ∧ PositiveDefinite phi ∧
        ∀ z, Phi (finiteAbelianWeylOperator W z : Mat d) = phi z • (finiteAbelianWeylOperator W z : Mat d)) ∧
    (∀ phi : H × CharacterGroup H → ℂ, phi 0 = 1 → PositiveDefinite phi →
      IsChannel (finiteAbelianWeylMultiplier W phi) ∧
      WeylCovariant W (finiteAbelianWeylMultiplier W phi) ∧
      ∀ z, finiteAbelianWeylMultiplier W phi (finiteAbelianWeylOperator W z : Mat d) =
        phi z • (finiteAbelianWeylOperator W z : Mat d)) := by
  -- any map agreeing with `phi` on the Weyl basis, linearly, is the Fourier mixture
  have agree : ∀ (F : Mat d → Mat d) (p : CharacterGroup H × H → ℝ),
      (∀ X, F X = ∑ z : H × CharacterGroup H,
        (((X4WY.Wm W z)ᴴ * X).trace / d) • fourierCharacteristic p z • X4WY.Wm W z) →
      ∀ X, F X = fourierMixture W p X := by
    intro F p hF X
    rw [hF, X4WY.expand hd W hirr X, X4WY.fm_sum]
    simp_rw [X4WY.fm_W]
    congr 1
    ext1 z
    congr 2
    rw [← X4WY.expand hd W hirr X]
  refine ⟨⟨fun ⟨hch, hcov⟩ => ?_, fun ⟨phi, h0, hpd, hW⟩ => ?_⟩, fun phi h0 hpd => ?_⟩
  · obtain ⟨m, E, hK, hPhiE⟩ := hch
    obtain ⟨r, hr0, hr1, hmain⟩ := X4WY.fwd hd W hirr Phi m E hK hPhiE hcov
    set p : CharacterGroup H × H → ℝ := fun t => r (X4WY.jeq t)
    have hfm : ∀ X : Mat d, Phi X = fourierMixture W p X := by
      intro X
      rw [X4WY.fm_eq', hmain]
      simp only [p, Equiv.apply_symm_apply]
    have hs : ∑ t, p t = 1 := by
      rw [← hr1]; exact Fintype.sum_equiv X4WY.jeq _ _ (fun _ => rfl)
    refine ⟨fourierCharacteristic p, ?_, X4WY.fc_pd p (fun t => hr0 _), fun z => ?_⟩
    · rw [X4WY.fc_zero, hs]; simp
    · rw [hfm]; exact X4WY.fm_W W p z
  · obtain ⟨p, hp0, hp1, hpφ⟩ := X4WY.bochner phi h0 hpd
    have hfm : ∀ X : Mat d, Phi X = fourierMixture W p X := by
      apply agree
      intro X
      conv_lhs => rw [X4WY.expand hd W hirr X]
      rw [map_sum]
      apply Finset.sum_congr rfl; intro z _
      rw [map_smul, hW, hpφ]
    have hfun : (⇑Phi : Mat d → Mat d) = fourierMixture W p := funext hfm
    refine ⟨?_, ?_⟩
    · rw [hfun]; exact X4WY.fm_channel W p hp0 hp1
    · rw [hfun]; exact X4WY.fm_cov W p
  · obtain ⟨p, hp0, hp1, hpφ⟩ := X4WY.bochner phi h0 hpd
    have hfm : ∀ X : Mat d, finiteAbelianWeylMultiplier W phi X = fourierMixture W p X := by
      apply agree
      intro X
      simp only [finiteAbelianWeylMultiplier, hpφ, smul_smul]
    have hfun : finiteAbelianWeylMultiplier W phi = fourierMixture W p := funext hfm
    refine ⟨?_, ?_, fun z => ?_⟩
    · rw [hfun]; exact X4WY.fm_channel W p hp0 hp1
    · rw [hfun]; exact X4WY.fm_cov W p
    · rw [hfun, X4WY.fm_W, hpφ]

end
