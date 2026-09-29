-- Prove2me | solution 1 for ValuationSubring.exists_monoidHom_decompositionSubgroup_zmod_two_eq_one_of_mem_inertiaSubgroupIn_ne_one_of_isFrobeniusAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/c2af3edf-d27d-5809-931c-70c6a9f99293

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_ValuationSubring_residueField_charP_of_liesOverPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_monoidHom_decompositionSubgroup_zmod_two_eq_one_of_mem_inertiaSubgroupIn_ne_one_of_isFrobeniusAt

set_option autoImplicit false

open IsLocalRing Polynomial

namespace S2ParityChar

section Counting

variable {κ : Type*} [Field κ] (r : ℕ) [Fact r.Prime] [CharP κ r]

private theorem _root_.S2ParityChar.one_lt : 1 < r := (Fact.out : r.Prime).one_lt

p2m_export "S2ParityChar" "one_lt"
private theorem natCast_pow_eq (n : ℕ) : ((n : κ)) ^ r = n := by
  have h := map_natCast (frobenius κ r) n
  rwa [frobenius_def] at h

private theorem natCast_pow_sq_eq (n : ℕ) : ((n : κ)) ^ (r ^ 2) = n := by
  rw [sq, pow_mul, natCast_pow_eq r n, natCast_pow_eq r n]

private theorem exists_natCast_of_pow_eq {y : κ} (hy : y ^ r = y) : ∃ n : ℕ, (n : κ) = y := by
  classical
  have hr := one_lt r
  have hf0 : (X ^ r - X : κ[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero κ hr
  have hdeg : (X ^ r - X : κ[X]).natDegree = r := FiniteField.X_pow_card_sub_X_natDegree_eq κ hr
  have hroot : ∀ z : κ, z ^ r = z → z ∈ (X ^ r - X : κ[X]).roots := fun z hz => by
    rw [mem_roots hf0, IsRoot, eval_sub, eval_pow, eval_X, hz, sub_self]
  let Z : Finset κ := (Finset.range r).image (fun n : ℕ => (n : κ))
  have hZcard : Z.card = r := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro a ha b hb hab
    have h := (CharP.natCast_eq_natCast κ r).mp hab
    rw [Nat.ModEq, Nat.mod_eq_of_lt (Finset.mem_coe.mp ha |> Finset.mem_range.mp),
      Nat.mod_eq_of_lt (Finset.mem_coe.mp hb |> Finset.mem_range.mp)] at h
    exact h
  by_contra hne
  push Not at hne
  have hyZ : y ∉ Z := by
    intro h
    obtain ⟨n, -, hn⟩ := Finset.mem_image.mp h
    exact hne n hn
  have hsub : (insert y Z).val ⊆ (X ^ r - X : κ[X]).roots := by
    intro z hz
    rw [Finset.insert_val_of_notMem hyZ, Multiset.mem_cons] at hz
    rcases hz with rfl | hz
    · exact hroot _ hy
    · obtain ⟨n, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_val.mp hz)
      exact hroot _ (natCast_pow_eq r n)
  have hle := card_le_degree_of_subset_roots hsub
  rw [Finset.card_insert_of_notMem hyZ, hZcard, hdeg] at hle
  omega

private theorem exists_omega [IsAlgClosed κ] : ∃ ω : κ, ω ^ (r ^ 2) = ω ∧ ω ^ r ≠ ω := by
  classical
  have hr := one_lt r
  have hr2 : 1 < r ^ 2 := by nlinarith
  have hg0 : (X ^ (r ^ 2) - X : κ[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero κ hr2
  have hgdeg : (X ^ (r ^ 2) - X : κ[X]).natDegree = r ^ 2 := FiniteField.X_pow_card_sub_X_natDegree_eq κ hr2
  have hf0 : (X ^ r - X : κ[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero κ hr
  have hfdeg : (X ^ r - X : κ[X]).natDegree = r := FiniteField.X_pow_card_sub_X_natDegree_eq κ hr
  have hsep : (X ^ (r ^ 2) - X : κ[X]).Separable := galois_poly_separable r (r ^ 2) (dvd_pow_self r two_ne_zero)
  have hcard : Fintype.card ((X ^ (r ^ 2) - X : κ[X]).rootSet κ) = r ^ 2 := by
    rw [card_rootSet_eq_natDegree hsep (IsAlgClosed.splits _), hgdeg]
  by_contra h
  push Not at h
  let Z : Finset κ := ((X ^ (r ^ 2) - X : κ[X]).rootSet κ).toFinset
  have hZ : Z.val ⊆ (X ^ r - X : κ[X]).roots := by
    intro z hz
    have hz' : z ∈ (X ^ (r ^ 2) - X : κ[X]).rootSet κ := Set.mem_toFinset.mp (Finset.mem_val.mp hz)
    rw [mem_rootSet] at hz'
    have hz2 : z ^ (r ^ 2) = z := by
      have e := hz'.2
      simp only [map_sub, map_pow, aeval_X] at e
      exact sub_eq_zero.mp e
    rw [mem_roots hf0, IsRoot, eval_sub, eval_pow, eval_X, h z hz2, sub_self]
  have hle := card_le_degree_of_subset_roots hZ
  rw [Set.toFinset_card, hcard, hfdeg] at hle
  nlinarith

end Counting

end S2ParityChar

open S2ParityChar in
theorem solution
    (r : ℕ) [Fact r.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r) :
    ∃ χ : ↥(A.decompositionSubgroup ℚ) →* Multiplicative (ZMod 2),
      (∀ τ : ↥(A.decompositionSubgroup ℚ),
          (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A.inertiaSubgroupIn ℚ → χ τ = 1) ∧
      (∀ φ : ↥(A.decompositionSubgroup ℚ),
          A.IsFrobeniusAt (φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) r → χ φ ≠ 1) ∧
      (∀ σ : ↥(A.decompositionSubgroup ℚ),
          χ σ = 1 ↔ ∀ x : ResidueField ↥A, x ^ (r ^ 2) = x → σ • x = x) := by
  classical
  haveI : CharP (ResidueField ↥A) r := ValuationSubring.residueField_charP_of_liesOverPrime A Fact.out hA
  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField A
  obtain ⟨ω, hω2, hω⟩ := S2ParityChar.exists_omega (κ := ResidueField ↥A) r

  have hcast : ∀ (σ : ↥(A.decompositionSubgroup ℚ)) (n : ℕ), σ • ((n : ResidueField ↥A)) = n := by
    intro σ n
    have h := map_natCast (MulSemiringAction.toRingHom ↥(A.decompositionSubgroup ℚ) (ResidueField ↥A) σ) n
    rwa [MulSemiringAction.toRingHom_apply] at h
  have hfix : ∀ (σ : ↥(A.decompositionSubgroup ℚ)) (y : ResidueField ↥A), y ^ r = y → σ • y = y := by
    intro σ y hy
    obtain ⟨n, rfl⟩ := S2ParityChar.exists_natCast_of_pow_eq r hy
    exact hcast σ n

  have hdich : ∀ σ : ↥(A.decompositionSubgroup ℚ), σ • ω = ω ∨ σ • ω = ω ^ r := by
    intro σ
    have hs : σ • (ω + ω ^ r) = ω + ω ^ r :=
      hfix σ _ (by rw [add_pow_char, ← pow_mul, ← sq, hω2, add_comm])
    have hp : σ • (ω * ω ^ r) = ω * ω ^ r :=
      hfix σ _ (by rw [mul_pow, ← pow_mul, ← sq, hω2, mul_comm])
    have h2 : (σ • ω) ^ 2 = (ω + ω ^ r) * (σ • ω) - ω * ω ^ r := by
      have e : ω ^ 2 = (ω + ω ^ r) * ω - ω * ω ^ r := by ring
      rw [← smul_pow', e, smul_sub, hp, smul_mul', hs]
    have key : (σ • ω - ω) * (σ • ω - ω ^ r) = 0 := by linear_combination h2
    rcases mul_eq_zero.mp key with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (sub_eq_zero.mp h)
  have hne : ∀ σ : ↥(A.decompositionSubgroup ℚ), σ • ω = ω ^ r → σ • ω ≠ ω := fun σ h => by rw [h]; exact hω

  let χ : ↥(A.decompositionSubgroup ℚ) →* Multiplicative (ZMod 2) :=
    { toFun := fun σ => if σ • ω = ω then 1 else Multiplicative.ofAdd 1
      map_one' := by simp only [one_smul, if_true]
      map_mul' := by
        intro σ τ
        have hστ : (σ * τ) • ω = σ • (τ • ω) := mul_smul σ τ ω
        rcases hdich σ with hσ | hσ <;> rcases hdich τ with hτ | hτ
        · have h1 : (σ * τ) • ω = ω := by rw [hστ, hτ, hσ]
          simp only [h1, hσ, hτ, if_true, one_mul]
        · have h1 : (σ * τ) • ω = ω ^ r := by rw [hστ, hτ, smul_pow', hσ]
          rw [if_neg (hne _ h1), if_pos hσ, if_neg (hne _ hτ), one_mul]
        · have h1 : (σ * τ) • ω = ω ^ r := by rw [hστ, hτ, hσ]
          rw [if_neg (hne _ h1), if_neg (hne _ hσ), if_pos hτ, mul_one]
        · have h1 : (σ * τ) • ω = ω := by rw [hστ, hτ, smul_pow', hσ, ← pow_mul, ← sq, hω2]
          rw [if_pos h1, if_neg (hne _ hσ), if_neg (hne _ hτ), ← ofAdd_add]
          rfl }
  have hχ : ∀ σ, χ σ = if σ • ω = ω then 1 else Multiplicative.ofAdd 1 := fun σ => rfl
  have hone : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide
  refine ⟨χ, ?_, ?_, ?_⟩
  ·
    intro τ hτ
    unfold ValuationSubring.inertiaSubgroupIn at hτ
    obtain ⟨τ', hτ', hττ'⟩ := Subgroup.mem_map.mp hτ
    have e : τ' = τ := Subtype.ext hττ'
    subst e
    have hk : MulSemiringAction.toRingAut ↥(A.decompositionSubgroup ℚ) (ResidueField ↥A) τ' = 1 :=
      MonoidHom.mem_ker.mp hτ'
    have hfixω : τ' • ω = ω := by
      have h := congrArg (fun e : RingAut (ResidueField ↥A) => e ω) hk
      simpa [MulSemiringAction.toRingAut_apply] using h
    rw [hχ, if_pos hfixω]
  ·
    intro φ hφ
    have h := hφ.smul_residue_eq ω
    have e : (⟨(φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), hφ.mem_decompositionSubgroup⟩ :
        ↥(A.decompositionSubgroup ℚ)) = φ := Subtype.ext rfl
    rw [e] at h
    rw [hχ, if_neg (hne _ h)]
    exact hone
  ·
    intro σ
    constructor
    · intro h1 x hx
      have hσω : σ • ω = ω := by
        by_contra hc
        rw [hχ, if_neg hc] at h1
        exact hone h1

      have hr := S2ParityChar.one_lt r
      have hr2 : 1 < r ^ 2 := by nlinarith
      have hg0 : (X ^ (r ^ 2) - X : (ResidueField ↥A)[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero _ hr2
      have hgdeg : (X ^ (r ^ 2) - X : (ResidueField ↥A)[X]).natDegree = r ^ 2 :=
        FiniteField.X_pow_card_sub_X_natDegree_eq _ hr2
      have hroot : ∀ z : ResidueField ↥A, z ^ (r ^ 2) = z → z ∈ (X ^ (r ^ 2) - X : (ResidueField ↥A)[X]).roots :=
        fun z hz => by rw [mem_roots hg0, IsRoot, eval_sub, eval_pow, eval_X, hz, sub_self]
      let emb : ℕ × ℕ → ResidueField ↥A := fun ab => (ab.1 : ResidueField ↥A) + (ab.2 : ResidueField ↥A) * ω
      let Z : Finset (ResidueField ↥A) := ((Finset.range r) ×ˢ (Finset.range r)).image emb
      have hinj : Set.InjOn emb ↑((Finset.range r) ×ˢ (Finset.range r)) := by
        rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' h
        simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range] at hab hab'
        simp only [emb] at h
        have hb : (b : ResidueField ↥A) = b' := by
          by_contra hbb
          have hsub : ((b : ResidueField ↥A) - b') ≠ 0 := sub_ne_zero.mpr hbb
          have hωeq : ω = ((a' : ResidueField ↥A) - a) / ((b : ResidueField ↥A) - b') := by
            rw [eq_div_iff hsub]; linear_combination h
          apply hω
          rw [hωeq, div_pow, sub_pow_char, sub_pow_char, S2ParityChar.natCast_pow_eq r, S2ParityChar.natCast_pow_eq r,
            S2ParityChar.natCast_pow_eq r, S2ParityChar.natCast_pow_eq r]
        have ha : (a : ResidueField ↥A) = a' := by rw [hb] at h; linear_combination h
        have ha' := (CharP.natCast_eq_natCast (ResidueField ↥A) r).mp ha
        have hb' := (CharP.natCast_eq_natCast (ResidueField ↥A) r).mp hb
        rw [Nat.ModEq, Nat.mod_eq_of_lt hab.1, Nat.mod_eq_of_lt hab'.1] at ha'
        rw [Nat.ModEq, Nat.mod_eq_of_lt hab.2, Nat.mod_eq_of_lt hab'.2] at hb'
        exact Prod.ext ha' hb'
      have hZcard : Z.card = r ^ 2 := by
        rw [Finset.card_image_of_injOn hinj, Finset.card_product, Finset.card_range, sq]
      have hZroots : ∀ z ∈ Z, z ^ (r ^ 2) = z := by
        intro z hz
        obtain ⟨⟨a, b⟩, -, rfl⟩ := Finset.mem_image.mp hz
        simp only [emb]
        rw [add_pow_char_pow, mul_pow, hω2, S2ParityChar.natCast_pow_sq_eq r, S2ParityChar.natCast_pow_sq_eq r]
      have hxZ : x ∈ Z := by
        by_contra hxZ
        have hsub : (insert x Z).val ⊆ (X ^ (r ^ 2) - X : (ResidueField ↥A)[X]).roots := by
          intro z hz
          rw [Finset.insert_val_of_notMem hxZ, Multiset.mem_cons] at hz
          rcases hz with rfl | hz
          · exact hroot _ hx
          · exact hroot _ (hZroots _ (Finset.mem_val.mp hz))
        have hle := card_le_degree_of_subset_roots hsub
        rw [Finset.card_insert_of_notMem hxZ, hZcard, hgdeg] at hle
        omega
      obtain ⟨⟨a, b⟩, -, rfl⟩ := Finset.mem_image.mp hxZ
      simp only [emb]
      rw [smul_add, smul_mul', hcast, hcast, hσω]
    · intro h
      rw [hχ, if_pos (h ω hω2)]

#print axioms solution

end S_ValuationSubring_exists_monoidHom_decompositionSubgroup_zmod_two_eq_one_of_mem_inertiaSubgroupIn_ne_one_of_isFrobeniusAt
end P2MW
export P2MW.S_ValuationSubring_exists_monoidHom_decompositionSubgroup_zmod_two_eq_one_of_mem_inertiaSubgroupIn_ne_one_of_isFrobeniusAt (solution)
