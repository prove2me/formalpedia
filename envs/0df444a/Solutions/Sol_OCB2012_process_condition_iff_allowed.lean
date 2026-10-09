-- Prove2me | solution 1 for OCB2012.process_condition_iff_allowed
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-08T23:31:38.598744+00:00
-- url     : https://prove2.me/submissions/a32b848a-b440-42b2-9144-707593fb71dd

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_OCB2012_defs
import Theorems.Thm_QInfo_expand_of_trace_orthogonal
import Theorems.Thm_QInfo_exists_posSemidef_one_add_smul

open Matrix
open scoped Kronecker ComplexOrder

namespace OCB2012Sol
open OCB2012

/-! ### Hilbert–Schmidt bases -/

lemma HSBasis.σ_none {X : Type*} [Fintype X] [DecidableEq X] (B : HSBasis X) : B.σ none = 1 := rfl

lemma HSBasis.σ_herm {X : Type*} [Fintype X] [DecidableEq X] (B : HSBasis X) (μ : Option B.ι) :
    (B.σ μ).IsHermitian := by
  cases μ with
  | none => exact isHermitian_one
  | some j => exact B.isHermitian j

lemma HSBasis.trace_σ {X : Type*} [Fintype X] [DecidableEq X] (B : HSBasis X) (μ : Option B.ι) :
    (B.σ μ).trace = if μ = none then (Fintype.card X : ℂ) else 0 := by
  cases μ with
  | none => simp [HSBasis.σ]
  | some j => simp [HSBasis.σ, B.trace_eq_zero j]

lemma HSBasis.trace_σ_mul {X : Type*} [Fintype X] [DecidableEq X] (B : HSBasis X)
    (μ μ' : Option B.ι) :
    (B.σ μ * B.σ μ').trace = if μ = μ' then (Fintype.card X : ℂ) else 0 := by
  cases μ with
  | none => cases μ' with
    | none => simp [HSBasis.σ]
    | some j => simp [HSBasis.σ, B.trace_eq_zero j]
  | some i => cases μ' with
    | none => simp [HSBasis.σ, B.trace_eq_zero i]
    | some j => simp [HSBasis.σ, B.trace_mul i j]

lemma HSBasis.card_ne_zero {X : Type*} [Fintype X] [DecidableEq X] (B : HSBasis X) :
    Fintype.card X ≠ 0 := by
  intro h; have := B.card_eq; rw [h] at this; simp at this

/-- Products `σ_μ ⊗ σ_ν` of two Hilbert–Schmidt bases expand every operator on `X1 × X2`. -/
lemma HSBasis.expand_prod {X1 X2 : Type*} [Fintype X1] [DecidableEq X1] [Fintype X2]
    [DecidableEq X2] (B1 : HSBasis X1) (B2 : HSBasis X2) (M : Matrix (X1 × X2) (X1 × X2) ℂ) :
    M = (Fintype.card (X1 × X2) : ℂ)⁻¹ •
      ∑ p : Option B1.ι × Option B2.ι, ((B1.σ p.1 ⊗ₖ B2.σ p.2) * M).trace • (B1.σ p.1 ⊗ₖ B2.σ p.2) := by
  refine QInfo.expand_of_trace_orthogonal (fun p : Option B1.ι × Option B2.ι => B1.σ p.1 ⊗ₖ B2.σ p.2) ?_ ?_ M
  · rintro ⟨μ, ν⟩ ⟨μ', ν'⟩
    simp only [← mul_kronecker_mul, trace_kronecker, HSBasis.trace_σ_mul, Fintype.card_prod,
      Prod.mk.injEq]
    split_ifs <;> simp_all
  · rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_option, Fintype.card_option,
      B1.card_eq, B2.card_eq]; ring

/-! ### Linearity of `prob` -/

variable {a1 a2 b1 b2 : Type*} [Fintype a1] [Fintype a2] [Fintype b1] [Fintype b2]
  [DecidableEq a1] [DecidableEq a2] [DecidableEq b1] [DecidableEq b2]

lemma prob_add_left' (W : Matrix ((a1 × a2) × (b1 × b2)) ((a1 × a2) × (b1 × b2)) ℂ)
    (MA MA' : Matrix (a1 × a2) (a1 × a2) ℂ) (MB : Matrix (b1 × b2) (b1 × b2) ℂ) :
    prob W (MA + MA') MB = prob W MA MB + prob W MA' MB := by
  simp only [prob, add_kronecker, Matrix.mul_add, trace_add]

lemma prob_add_right' (W : Matrix ((a1 × a2) × (b1 × b2)) ((a1 × a2) × (b1 × b2)) ℂ)
    (MA : Matrix (a1 × a2) (a1 × a2) ℂ) (MB MB' : Matrix (b1 × b2) (b1 × b2) ℂ) :
    prob W MA (MB + MB') = prob W MA MB + prob W MA MB' := by
  simp only [prob, kronecker_add, Matrix.mul_add, trace_add]

lemma prob_smul_left' (W : Matrix ((a1 × a2) × (b1 × b2)) ((a1 × a2) × (b1 × b2)) ℂ) (r : ℂ)
    (MA : Matrix (a1 × a2) (a1 × a2) ℂ) (MB : Matrix (b1 × b2) (b1 × b2) ℂ) :
    prob W (r • MA) MB = r * prob W MA MB := by
  simp only [prob, smul_kronecker, Matrix.mul_smul, trace_smul, smul_eq_mul]

lemma prob_smul_right' (W : Matrix ((a1 × a2) × (b1 × b2)) ((a1 × a2) × (b1 × b2)) ℂ) (r : ℂ)
    (MA : Matrix (a1 × a2) (a1 × a2) ℂ) (MB : Matrix (b1 × b2) (b1 × b2) ℂ) :
    prob W MA (r • MB) = r * prob W MA MB := by
  simp only [prob, kronecker_smul, Matrix.mul_smul, trace_smul, smul_eq_mul]

lemma prob_sum_left {κ : Type*} (s : Finset κ)
    (W : Matrix ((a1 × a2) × (b1 × b2)) ((a1 × a2) × (b1 × b2)) ℂ)
    (f : κ → Matrix (a1 × a2) (a1 × a2) ℂ) (MB : Matrix (b1 × b2) (b1 × b2) ℂ) :
    prob W (∑ i ∈ s, f i) MB = ∑ i ∈ s, prob W (f i) MB := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [prob]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, prob_add_left', ih]

lemma prob_sum_right {κ : Type*} (s : Finset κ)
    (W : Matrix ((a1 × a2) × (b1 × b2)) ((a1 × a2) × (b1 × b2)) ℂ)
    (MA : Matrix (a1 × a2) (a1 × a2) ℂ) (f : κ → Matrix (b1 × b2) (b1 × b2) ℂ) :
    prob W MA (∑ i ∈ s, f i) = ∑ i ∈ s, prob W MA (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [prob]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, prob_add_right', ih]

/-! ### Partial traces -/

lemma trace_kron_one_mul' {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (X : Matrix α α ℂ) (M : Matrix (α × β) (α × β) ℂ) :
    ((X ⊗ₖ (1 : Matrix β β ℂ)) * M).trace = (X * ptrace₂ M).trace := by
  simp only [trace, diag, mul_apply, Fintype.sum_prod_type, kronecker_apply, one_apply,
    ptrace₂, of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [mul_ite, ite_mul]

lemma ptrace₂_kron' {α β : Type*} [Fintype β] (A : Matrix α α ℂ) (B : Matrix β β ℂ) :
    ptrace₂ (A ⊗ₖ B) = B.trace • A := by
  ext i j
  simp [ptrace₂, kroneckerMap_apply, trace, Finset.mul_sum, mul_comm]

lemma ptrace₂_add' {α β : Type*} [Fintype β] (M N : Matrix (α × β) (α × β) ℂ) :
    ptrace₂ (M + N) = ptrace₂ M + ptrace₂ N := by
  ext i j; simp [ptrace₂, Finset.sum_add_distrib]

lemma ptrace₂_smul' {α β : Type*} [Fintype β] (r : ℂ) (M : Matrix (α × β) (α × β) ℂ) :
    ptrace₂ (r • M) = r • ptrace₂ M := by
  ext i j; simp [ptrace₂, Finset.mul_sum]

lemma ptrace₂_one {α β : Type*} [Fintype β] [DecidableEq α] [DecidableEq β] :
    ptrace₂ (1 : Matrix (α × β) (α × β) ℂ) = (Fintype.card β : ℂ) • 1 := by
  ext i j
  by_cases h : i = j <;> simp [ptrace₂, one_apply, h]

/-- The maximally mixed CJ matrix `𝟙/d₂` is CPTP. -/
lemma cptp_mix {x1 x2 : Type*} [Fintype x1] [Fintype x2] [DecidableEq x1] [DecidableEq x2]
    (h2 : Fintype.card x2 ≠ 0) :
    IsCPTP_CJ ((((Fintype.card x2 : ℝ)⁻¹ : ℝ) : ℂ) • (1 : Matrix (x1 × x2) (x1 × x2) ℂ)) := by
  refine ⟨PosSemidef.one.smul (Complex.zero_le_real.mpr (by positivity)), ?_⟩
  rw [ptrace₂_smul', ptrace₂_one, smul_smul]
  push_cast
  rw [inv_mul_cancel₀ (by exact_mod_cast h2), one_smul]

/-- Condition (5) extends from CPTP maps to all Hermitian `X` with `Tr₂ X = 0` (App. C:
"condition (5) can be equivalently imposed on arbitrary matrices of the form (18)"). -/
lemma perturb {x1 x2 : Type*} [Fintype x1] [Fintype x2] [DecidableEq x1] [DecidableEq x2]
    (h2 : Fintype.card x2 ≠ 0) (F : Matrix (x1 × x2) (x1 × x2) ℂ → ℂ)
    (hadd : ∀ M N, F (M + N) = F M + F N) (hsmul : ∀ (r : ℂ) M, F (r • M) = r * F M)
    (hconst : ∀ M N, IsCPTP_CJ M → IsCPTP_CJ N → F M = F N)
    (X : Matrix (x1 × x2) (x1 × x2) ℂ) (hX : X.IsHermitian) (hX0 : ptrace₂ X = 0) : F X = 0 := by
  obtain ⟨t, ht, hpsd⟩ := QInfo.exists_posSemidef_one_add_smul X hX
  set c : ℝ := (Fintype.card x2 : ℝ)⁻¹
  have hc : 0 < c := by positivity
  set M0 := ((c : ℝ) : ℂ) • (1 : Matrix (x1 × x2) (x1 × x2) ℂ)
  have hM0 : IsCPTP_CJ M0 := cptp_mix h2
  have hM : IsCPTP_CJ (M0 + ((c * t : ℝ) : ℂ) • X) := by
    refine ⟨?_, ?_⟩
    · have : M0 + ((c * t : ℝ) : ℂ) • X = (c : ℂ) • (1 + (t : ℂ) • X) := by
        rw [smul_add, smul_smul]; push_cast; rfl
      rw [this]; exact hpsd.smul (Complex.zero_le_real.mpr hc.le)
    · rw [ptrace₂_add', hM0.2, ptrace₂_smul', hX0, smul_zero, add_zero]
  have := hconst _ _ hM hM0
  simp only [hadd, hsmul] at this
  have hct : ((c * t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (mul_pos hc ht).ne'
  exact (mul_eq_zero.mp (by linear_combination this)).resolve_left hct

end OCB2012Sol

open OCB2012 OCB2012Sol in
theorem solution {a1 a2 b1 b2 : Type*} [Fintype a1] [Fintype a2]
    [Fintype b1] [Fintype b2] [DecidableEq a1] [DecidableEq a2] [DecidableEq b1] [DecidableEq b2]
    (BA1 : HSBasis a1) (BA2 : HSBasis a2) (BB1 : HSBasis b1) (BB2 : HSBasis b2)
    (W : Matrix ((a1 × a2) × (b1 × b2)) ((a1 × a2) × (b1 × b2)) ℂ) (hW : W.IsHermitian) :
    (∀ (MA : Matrix (a1 × a2) (a1 × a2) ℂ) (MB : Matrix (b1 × b2) (b1 × b2) ℂ),
        IsCPTP_CJ MA → IsCPTP_CJ MB → prob W MA MB = 1) ↔
      (W.trace = (Fintype.card a2 * Fintype.card b2 : ℂ) ∧
        ∀ μ ν l γ, ¬ AllowedType μ.isSome ν.isSome l.isSome γ.isSome →
          (W * ((BA1.σ μ ⊗ₖ BA2.σ ν) ⊗ₖ (BB1.σ l ⊗ₖ BB2.σ γ))).trace = 0) := by
  have hA2 := (HSBasis.card_ne_zero BA2)
  have hB2 := (HSBasis.card_ne_zero BB2)
  have hA1 := (HSBasis.card_ne_zero BA1)
  have hB1 := (HSBasis.card_ne_zero BB1)
  have hprob11 : prob W (1 : Matrix (a1 × a2) (a1 × a2) ℂ) (1 : Matrix (b1 × b2) (b1 × b2) ℂ) =
      W.trace := by
    rw [prob, one_kronecker_one, Matrix.mul_one]
  constructor
  · intro h5
    set MA0 := ((((Fintype.card a2 : ℝ)⁻¹ : ℝ) : ℂ) • (1 : Matrix (a1 × a2) (a1 × a2) ℂ))
    set MB0 := ((((Fintype.card b2 : ℝ)⁻¹ : ℝ) : ℂ) • (1 : Matrix (b1 × b2) (b1 × b2) ℂ))
    have hMA0 : IsCPTP_CJ MA0 := cptp_mix hA2
    have hMB0 : IsCPTP_CJ MB0 := cptp_mix hB2
    have hone_A : (1 : Matrix (a1 × a2) (a1 × a2) ℂ) = (Fintype.card a2 : ℂ) • MA0 := by
      rw [smul_smul]; push_cast; rw [mul_inv_cancel₀ (by exact_mod_cast hA2), one_smul]
    have hone_B : (1 : Matrix (b1 × b2) (b1 × b2) ℂ) = (Fintype.card b2 : ℂ) • MB0 := by
      rw [smul_smul]; push_cast; rw [mul_inv_cancel₀ (by exact_mod_cast hB2), one_smul]
    -- Hermitian `X` with `Tr_{A2} X = 0` contribute nothing, and likewise for Bob.
    have kerA : ∀ X, X.IsHermitian → ptrace₂ X = 0 → ∀ MB, IsCPTP_CJ MB → prob W X MB = 0 :=
      fun X hX hX0 MB hMB => perturb hA2 (fun M => prob W M MB) (fun M N => prob_add_left' _ _ _ _)
        (fun r M => prob_smul_left' _ _ _ _)
        (fun M N hM hN => by simp only [h5 _ _ hM hMB, h5 _ _ hN hMB]) X hX hX0
    have kerB : ∀ Y, Y.IsHermitian → ptrace₂ Y = 0 → ∀ MA, IsCPTP_CJ MA → prob W MA Y = 0 :=
      fun Y hY hY0 MA hMA => perturb hB2 (fun M => prob W MA M) (fun M N => prob_add_right' _ _ _ _)
        (fun r M => prob_smul_right' _ _ _ _)
        (fun M N hM hN => by simp only [h5 _ _ hMA hM, h5 _ _ hMA hN]) Y hY hY0
    have kerAB : ∀ X, X.IsHermitian → ptrace₂ X = 0 → ∀ Y, Y.IsHermitian → ptrace₂ Y = 0 →
        prob W X Y = 0 :=
      fun X hX hX0 Y hY hY0 => perturb hB2 (fun M => prob W X M)
        (fun M N => prob_add_right' _ _ _ _) (fun r M => prob_smul_right' _ _ _ _)
        (fun M N hM hN => by simp only [kerA X hX hX0 _ hM, kerA X hX hX0 _ hN]) Y hY hY0
    refine ⟨?_, ?_⟩
    · have h := h5 _ _ hMA0 hMB0
      rw [prob_smul_left', prob_smul_right', hprob11] at h
      have hA2' : (Fintype.card a2 : ℂ) ≠ 0 := by exact_mod_cast hA2
      have hB2' : (Fintype.card b2 : ℂ) ≠ 0 := by exact_mod_cast hB2
      push_cast at h
      field_simp at h
      linear_combination h
    · intro μ ν l γ hna
      show prob W _ _ = 0
      have hXA : ∀ μ j, ptrace₂ (BA1.σ μ ⊗ₖ BA2.σ (some j)) = 0 := by
        intro μ j; rw [ptrace₂_kron', (HSBasis.trace_σ BA2)]; simp
      have hXB : ∀ l j, ptrace₂ (BB1.σ l ⊗ₖ BB2.σ (some j)) = 0 := by
        intro l j; rw [ptrace₂_kron', (HSBasis.trace_σ BB2)]; simp
      have hHA : ∀ μ ν, (BA1.σ μ ⊗ₖ BA2.σ ν).IsHermitian := fun μ ν => by
        simp only [IsHermitian, conjTranspose_kronecker, ((HSBasis.σ_herm BA1) μ).eq, ((HSBasis.σ_herm BA2) ν).eq]
      have hHB : ∀ l γ, (BB1.σ l ⊗ₖ BB2.σ γ).IsHermitian := fun l γ => by
        simp only [IsHermitian, conjTranspose_kronecker, ((HSBasis.σ_herm BB1) l).eq, ((HSBasis.σ_herm BB2) γ).eq]
      cases ν with
      | some j =>
        cases γ with
        | some k => exact kerAB _ (hHA _ _) (hXA _ _) _ (hHB _ _) (hXB _ _)
        | none =>
          cases l with
          | some k => simp [AllowedType] at hna
          | none =>
            rw [HSBasis.σ_none, HSBasis.σ_none, one_kronecker_one, hone_B, prob_smul_right',
              kerA _ (hHA _ _) (hXA _ _) _ hMB0, mul_zero]
      | none =>
        cases μ with
        | some i => simp [AllowedType] at hna
        | none =>
          cases γ with
          | none => simp [AllowedType] at hna
          | some k =>
            rw [HSBasis.σ_none, HSBasis.σ_none, one_kronecker_one, hone_A, prob_smul_left',
              kerB _ (hHB _ _) (hXB _ _) _ hMA0, mul_zero]
  · rintro ⟨hT, hZ⟩ MA MB hA hB
    -- Coefficients of a CPTP map with identity on the output: `a_{μ0} = d δ_{μ0}`.
    have haA : ∀ μ, ((BA1.σ μ ⊗ₖ BA2.σ none) * MA).trace =
        if μ = none then (Fintype.card a1 : ℂ) else 0 := by
      intro μ; rw [HSBasis.σ_none, trace_kron_one_mul', hA.2, Matrix.mul_one, (HSBasis.trace_σ BA1)]
    have haB : ∀ l, ((BB1.σ l ⊗ₖ BB2.σ none) * MB).trace =
        if l = none then (Fintype.card b1 : ℂ) else 0 := by
      intro l; rw [HSBasis.σ_none, trace_kron_one_mul', hB.2, Matrix.mul_one, (HSBasis.trace_σ BB1)]
    -- Each term of the double expansion vanishes unless all indices are `0`.
    have hterm : ∀ μ ν l γ, ((BB1.σ l ⊗ₖ BB2.σ γ) * MB).trace *
        (((BA1.σ μ ⊗ₖ BA2.σ ν) * MA).trace *
          prob W (BA1.σ μ ⊗ₖ BA2.σ ν) (BB1.σ l ⊗ₖ BB2.σ γ)) =
        if μ = none ∧ ν = none ∧ l = none ∧ γ = none then
          (Fintype.card a1 : ℂ) * ((Fintype.card b1 : ℂ) * W.trace) else 0 := by
      intro μ ν l γ
      have hz : ¬ AllowedType μ.isSome ν.isSome l.isSome γ.isSome →
          prob W (BA1.σ μ ⊗ₖ BA2.σ ν) (BB1.σ l ⊗ₖ BB2.σ γ) = 0 := hZ μ ν l γ
      cases ν with
      | some j =>
        cases γ with
        | some k => rw [hz (by simp [AllowedType])]; simp
        | none =>
          cases l with
          | none => rw [hz (by simp [AllowedType])]; simp
          | some k => rw [haB]; simp
      | none =>
        cases μ with
        | some i => rw [haA]; simp
        | none =>
          cases γ with
          | some k => rw [hz (by simp [AllowedType])]; simp
          | none =>
            cases l with
            | some k => rw [haB]; simp
            | none =>
              rw [haA, haB]
              simp only [HSBasis.σ_none, one_kronecker_one, hprob11]
              simp; ring
    rw [HSBasis.expand_prod BA1 BA2 MA, HSBasis.expand_prod BB1 BB2 MB, prob_smul_left', prob_smul_right',
      prob_sum_left]
    simp only [prob_smul_left', prob_sum_right, prob_smul_right', Fintype.sum_prod_type]
    simp only [hterm, ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rw [hT]
    simp only [Fintype.card_prod]; push_cast
    have : (Fintype.card a1 : ℂ) ≠ 0 := by exact_mod_cast hA1
    have : (Fintype.card a2 : ℂ) ≠ 0 := by exact_mod_cast hA2
    have : (Fintype.card b1 : ℂ) ≠ 0 := by exact_mod_cast hB1
    have : (Fintype.card b2 : ℂ) ≠ 0 := by exact_mod_cast hB2
    field_simp
