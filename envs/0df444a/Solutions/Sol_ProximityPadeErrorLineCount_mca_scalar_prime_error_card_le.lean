-- Prove2me | solution 1 for ProximityPadeErrorLineCount.mca_scalar_prime_error_card_le
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-10-04T16:33:25.494233+00:00
-- url     : https://prove2.me/submissions/90ca7803-fbb6-4b96-a878-2d93c1118ee2

import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Module.Pi
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring


namespace RemainderCodeword

noncomputable section
open scoped BigOperators
open Polynomial
variable {K : Type*} [Field K]

/-- Removing a monic locator factor from the modulus removes it from the remainder. -/
theorem locator_mul_remainder (lam Q Y : K[X]) (hlam : lam.Monic) (hQ : Q.Monic) :
    (lam*Y) %ₘ (lam*Q) = lam*(Y %ₘ Q) := by
  apply (Polynomial.div_modByMonic_unique (Y /ₘ Q) (lam*(Y %ₘ Q)) (hlam.mul hQ) ?_).2
  constructor
  · calc
      lam*(Y %ₘ Q)+(lam*Q)*(Y /ₘ Q) = lam*((Y %ₘ Q)+Q*(Y /ₘ Q)) := by ring
      _ = lam*Y := by rw [Polynomial.modByMonic_add_div]
  · by_cases hz : Y %ₘ Q = 0
    · simp only [hz, mul_zero, degree_zero]
      exact bot_lt_iff_ne_bot.mpr (Polynomial.degree_ne_bot.mpr (mul_ne_zero hlam.ne_zero hQ.ne_zero))
    · apply Polynomial.degree_lt_degree
      rw [Polynomial.natDegree_mul hlam.ne_zero hz,
        Polynomial.natDegree_mul hlam.ne_zero hQ.ne_zero]
      exact Nat.add_lt_add_left ((Polynomial.natDegree_lt_natDegree_iff hz).mpr
        (Polynomial.degree_modByMonic_lt Y hQ)) _

theorem locator_remainder_degree_iff (lam Q Y : K[X])
    (hlam : lam.Monic) (hQ : Q.Monic) (k : ℕ) (hk : 0<k) :
    ((lam*Y) %ₘ (lam*Q)).natDegree < k+lam.natDegree ↔
      (Y %ₘ Q).natDegree < k := by
  rw [locator_mul_remainder lam Q Y hlam hQ]
  by_cases hz : Y %ₘ Q=0
  · simp only [hz, mul_zero, natDegree_zero]
    omega
  · rw [Polynomial.natDegree_mul hlam.ne_zero hz]
    omega

theorem remainder_degree_iff_codeword (Q Y : K[X]) (hQ : Q.Monic)
    (k : ℕ) (hkQ : k≤Q.natDegree) :
    (Y %ₘ Q).natDegree < k ↔ ∃ f : K[X], f.natDegree<k ∧ Q ∣ Y-f := by
  constructor
  · intro h
    refine ⟨Y %ₘ Q, h, ?_⟩
    rw [Polynomial.modByMonic_eq_sub_mul_div]
    convert dvd_mul_right Q (Y /ₘ Q) using 1 <;> ring
  · rintro ⟨f, hf, hdiv⟩
    rw [Polynomial.modByMonic_eq_of_dvd_sub hQ hdiv,
      (Polynomial.modByMonic_eq_self_iff hQ).mpr (Polynomial.degree_lt_degree (hf.trans_le hkQ))]
    exact hf

/-- The codeword is on the exact complementary factor Q, with no support padding. -/
theorem split_locator_codeword_iff (lam Q Y : K[X])
    (hlam : lam.Monic) (hQ : Q.Monic) (k : ℕ) (hk : 0<k) (hkQ : k≤Q.natDegree) :
    ((lam*Y) %ₘ (lam*Q)).natDegree < k+lam.natDegree ↔
      ∃ f : K[X], f.natDegree<k ∧ Q ∣ Y-f := by
  rw [locator_remainder_degree_iff lam Q Y hlam hQ k hk]
  exact remainder_degree_iff_codeword Q Y hQ k hkQ

def nodal (S : Finset K) : K[X] := ∏ x ∈ S, (Polynomial.X-Polynomial.C x)

theorem nodal_monic (S : Finset K) : (nodal S).Monic :=
  Polynomial.monic_prod_X_sub_C id S

theorem nodal_natDegree (S : Finset K) : (nodal S).natDegree = S.card :=
  Polynomial.natDegree_finsetProd_X_sub_C_eq_card S id

theorem nodal_eval_zero (S : Finset K) {x : K} (hx : x∈S) : (nodal S).eval x = 0 := by
  classical
  simp only [nodal, Polynomial.eval_prod]
  apply Finset.prod_eq_zero hx
  simp

theorem nodal_dvd_iff (S : Finset K) (P : K[X]) :
    nodal S ∣ P ↔ ∀ x∈S, P.eval x=0 := by
  classical
  constructor
  · rintro ⟨Q, rfl⟩ x hx
    simp [Polynomial.eval_mul, nodal_eval_zero S hx]
  · intro h
    unfold nodal
    refine Finset.prod_dvd_of_coprime (fun x _ z _ hxz =>
      Polynomial.pairwise_coprime_X_sub_C Function.injective_id hxz) ?_
    intro x hx
    exact Polynomial.dvd_iff_isRoot.mpr (h x hx)

/-- The remainder criterion recovers a codeword on exactly S minus E. -/
theorem exact_support_remainder_iff [DecidableEq K]
    (S E : Finset K) (hES : E⊆S) (Y : K[X])
    (k : ℕ) (hk : 0<k) (hkS : k≤(S\E).card) :
    ((nodal E*Y) %ₘ nodal S).natDegree < k+E.card ↔
      ∃ f : K[X], f.natDegree<k ∧ ∀ x∈S\E, Y.eval x=f.eval x := by
  have hsplit : nodal S=nodal E*nodal (S\E) := by
    unfold nodal
    rw [mul_comm]
    exact (Finset.prod_sdiff hES).symm
  rw [hsplit, ← nodal_natDegree E,
    split_locator_codeword_iff _ _ _ (nodal_monic E) (nodal_monic (S\E)) k hk
      (by simpa only [nodal_natDegree] using hkS)]
  simp only [nodal_dvd_iff, Polynomial.eval_sub, sub_eq_zero]

def coefficientWindow (P : K[X]) (lo width : ℕ) : Fin width → K :=
  fun i => P.coeff (lo+i.val)

theorem coefficientWindow_zero_iff (P : K[X]) (lo n : ℕ)
    (hlo : 0<lo) (hln : lo≤n) (hP : P.natDegree<n) :
    coefficientWindow P lo (n-lo)=0 ↔ P.natDegree<lo := by
  constructor
  · intro hz
    by_contra hn
    have hle : lo≤P.natDegree := by omega
    let i : Fin (n-lo) := ⟨P.natDegree-lo, by omega⟩
    have hc := congrFun hz i
    change P.coeff (lo+(P.natDegree-lo))=0 at hc
    rw [Nat.add_sub_of_le hle] at hc
    have hzero : P=0 := Polynomial.leadingCoeff_eq_zero.mp (by simpa using hc)
    simp only [hzero, Polynomial.natDegree_zero] at hle
    omega
  · intro h
    ext i
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by change P.natDegree<lo+i.val; omega)

def remainderWindow (G Y : K[X]) (lo width : ℕ) (lam : K[X]) : Fin width → K :=
  coefficientWindow ((lam*Y) %ₘ G) lo width

theorem remainderWindow_word_add (G Y0 Y1 lam : K[X]) (t : K) (lo width : ℕ) :
    remainderWindow G (Y0+t • Y1) lo width lam =
      remainderWindow G Y0 lo width lam + t • remainderWindow G Y1 lo width lam := by
  ext i
  simp [remainderWindow, coefficientWindow, mul_add, mul_smul_comm,
    Polynomial.add_modByMonic, Polynomial.smul_modByMonic, Polynomial.coeff_add,
    Polynomial.coeff_smul]

theorem exact_support_window_iff [DecidableEq K]
    (S E : Finset K) (hES : E⊆S) (Y : K[X])
    (k : ℕ) (hk : 0<k) (hkS : k≤(S\E).card) :
    remainderWindow (nodal S) Y (k+E.card) (S.card-(k+E.card)) (nodal E)=0 ↔
      ∃ f : K[X], f.natDegree<k ∧ ∀ x∈S\E, Y.eval x=f.eval x := by
  have hcard := Finset.card_sdiff_add_card_eq_card hES
  have hSpos : 0<S.card := by omega
  have hrem : ((nodal E*Y) %ₘ nodal S).natDegree<S.card := by
    rw [← nodal_natDegree S]
    apply Polynomial.natDegree_modByMonic_lt _ (nodal_monic S)
    intro h
    have hd := congrArg Polynomial.natDegree h
    rw [nodal_natDegree, Polynomial.natDegree_one] at hd
    omega
  change coefficientWindow ((nodal E*Y) %ₘ nodal S) (k+E.card) (S.card-(k+E.card))=0 ↔ _
  rw [coefficientWindow_zero_iff _ _ _ (by omega) (by omega) hrem]
  exact exact_support_remainder_iff S E hES Y k hk hkS


end
end RemainderCodeword


namespace ProximityPadeParity

noncomputable section
open Polynomial

variable {K : Type*} [Field K]

def parity (S : Finset K) (k : ℕ) (Y : K[X]) : Fin (S.card-k) → K :=
  RemainderCodeword.remainderWindow (RemainderCodeword.nodal S) Y k (S.card-k) 1

theorem parity_affine (S : Finset K) (k : ℕ) (Y₀ Y₁ : K[X]) (γ : K) :
    parity S k (Y₀+γ • Y₁)=parity S k Y₀+γ • parity S k Y₁ :=
  RemainderCodeword.remainderWindow_word_add _ _ _ _ _ _ _

@[simp] theorem parity_zero (S : Finset K) (k : ℕ) : parity S k (0 : K[X])=0 := by
  ext i
  simp [parity, RemainderCodeword.remainderWindow, RemainderCodeword.coefficientWindow]

theorem parity_smul (S : Finset K) (k : ℕ) (Y : K[X]) (γ : K) :
    parity S k (γ • Y)=γ • parity S k Y := by
  simpa using parity_affine S k 0 Y γ

theorem parity_sub (S : Finset K) (k : ℕ) (Y₀ Y₁ : K[X]) :
    parity S k (Y₀-Y₁)=parity S k Y₀-parity S k Y₁ := by
  simpa only [neg_one_smul, sub_eq_add_neg] using parity_affine S k Y₀ Y₁ (-1)

theorem remainder_eval (S : Finset K) (Y : K[X]) {x : K} (hx : x∈S) :
    (Y %ₘ RemainderCodeword.nodal S).eval x=Y.eval x := by
  rw [Polynomial.modByMonic_eq_sub_mul_div, Polynomial.eval_sub, Polynomial.eval_mul,
    RemainderCodeword.nodal_eval_zero S hx, zero_mul, sub_zero]

theorem remainder_natDegree_lt (S : Finset K) (hS : 0<S.card) (Y : K[X]) :
    (Y %ₘ RemainderCodeword.nodal S).natDegree<S.card := by
  rw [← RemainderCodeword.nodal_natDegree S]
  apply Polynomial.natDegree_modByMonic_lt _ (RemainderCodeword.nodal_monic S)
  intro hz
  have h := congrArg Polynomial.natDegree hz
  rw [RemainderCodeword.nodal_natDegree, Polynomial.natDegree_one] at h
  omega

/-- The whole high coefficient window vanishes exactly for a globally coded word. -/
theorem parity_zero_iff [DecidableEq K] (S : Finset K) (k : ℕ)
    (hk : 0<k) (hkS : k≤S.card) (Y : K[X]) :
    parity S k Y=0 ↔ ∃ P : K[X], P.natDegree<k ∧ ∀ x∈S, Y.eval x=P.eval x := by
  simp only [parity, RemainderCodeword.remainderWindow, one_mul]
  rw [RemainderCodeword.coefficientWindow_zero_iff _ _ _ hk hkS
    (remainder_natDegree_lt S (hk.trans_le hkS) Y)]
  rw [RemainderCodeword.remainder_degree_iff_codeword _ _
    (RemainderCodeword.nodal_monic S) k (by simpa [RemainderCodeword.nodal_natDegree] using hkS)]
  simp only [RemainderCodeword.nodal_dvd_iff, Polynomial.eval_sub, sub_eq_zero]

theorem parity_low_degree [DecidableEq K] (S : Finset K) (k : ℕ)
    (hk : 0<k) (hkS : k≤S.card) (P : K[X]) (hP : P.natDegree<k) :
    parity S k P=0 := (parity_zero_iff S k hk hkS P).2 ⟨P,hP,fun _ _ => rfl⟩

/-- Prime-field-valued nodal evaluations force every coefficient of the remainder into
that subfield, by uniqueness and coefficientwise Frobenius. -/
theorem remainder_coeff_prime (p : ℕ) [Fact p.Prime] [CharP K p]
    (S : Finset K) (hcard : 0<S.card) (hS : ∀ x∈S, x^p=x) (Y : K[X])
    (hY : ∀ x∈S, Y.eval x ∈ (⊥ : Subfield K)) (j : ℕ) :
    (Y %ₘ RemainderCodeword.nodal S).coeff j ∈ (⊥ : Subfield K) := by
  let R := Y %ₘ RemainderCodeword.nodal S
  have hR : R.natDegree<S.card := remainder_natDegree_lt S hcard Y
  have hdeg (P : K[X]) (hP : P.natDegree<S.card) :
      P.degree<(S.card : WithBot ℕ) :=
    degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr hP)
  have heq : R.map (frobenius K p)=R := by
    apply Polynomial.eq_of_degrees_lt_of_eval_index_eq S
      (fun _ _ _ _ h => h) (hdeg _ (Polynomial.natDegree_map_le.trans_lt hR)) (hdeg _ hR)
    intro x hx
    have hfixed : frobenius K p x=x := hS x hx
    have hmap : (R.map (frobenius K p)).eval x=frobenius K p (R.eval x) := by
      simpa only [hfixed] using Polynomial.eval_map_apply (p := R) (frobenius K p) x
    rw [hmap]
    change (R.eval x)^p=R.eval x
    change ((Y %ₘ RemainderCodeword.nodal S).eval x)^p=
      (Y %ₘ RemainderCodeword.nodal S).eval x
    rw [remainder_eval S Y hx]
    exact (Subfield.mem_bot_iff_pow_eq_self K p).1 (hY x hx)
  apply (Subfield.mem_bot_iff_pow_eq_self K p).2
  have hc := congrArg (fun Q : K[X] => Q.coeff j) heq
  simpa only [Polynomial.coeff_map, frobenius_def] using hc

/-- A nonzero scalar prime-field error word produces scalar prime-field parity coordinates. -/
theorem parity_error_line (p : ℕ) [Fact p.Prime] [CharP K p] [DecidableEq K]
    (S : Finset K) (k : ℕ) (hk : 0<k) (hkS : k≤S.card)
    (hS : ∀ x∈S, x^p=x) (Y P : K[X]) (hP : P.natDegree<k)
    (η : K) (hη : η≠0)
    (hline : ∀ x∈S, (Y.eval x-P.eval x)/η ∈ (⊥ : Subfield K)) :
    ∃ v : Fin (S.card-k) → (⊥ : Subfield K),
      ∀ j, parity S k Y j=η*(v j : K) := by
  let N : K[X] := η⁻¹ • (Y-P)
  have hN : ∀ x∈S, N.eval x ∈ (⊥ : Subfield K) := by
    intro x hx
    simpa only [N, Polynomial.eval_smul, Polynomial.eval_sub, smul_eq_mul,
      div_eq_mul_inv, mul_comm] using hline x hx
  have hpN : ∀ j, parity S k N j ∈ (⊥ : Subfield K) := by
    intro j
    simpa only [parity, RemainderCodeword.remainderWindow, RemainderCodeword.coefficientWindow,
      one_mul] using remainder_coeff_prime p S (hk.trans_le hkS) hS N hN (k+j.val)
  refine ⟨fun j => ⟨parity S k N j,hpN j⟩, ?_⟩
  intro j
  change parity S k Y j=η*parity S k N j
  have hNpar : parity S k N=η⁻¹ • parity S k Y := by
    dsimp only [N]
    rw [parity_smul, parity_sub, parity_low_degree S k hk hkS P hP, sub_zero]
  rw [hNpar]
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp

end
end ProximityPadeParity



namespace ProximityPadeDependentCase

noncomputable section
open Polynomial

variable {K : Type*} [Field K]

/-- A globally coded affine relation leaves only its cancellation parameter exceptional. -/
theorem simultaneous_fit_of_dependent_word
    (S T : Finset K) (hTS : T ⊆ S) (Y₀ Y₁ C P : K[X]) (ρ γ : K) {k : ℕ}
    (hC : C.natDegree < k) (hP : P.natDegree < k)
    (hglobal : ∀ x ∈ S, C.eval x = Y₀.eval x - ρ * Y₁.eval x)
    (hfit : ∀ x ∈ T, P.eval x = Y₀.eval x + γ * Y₁.eval x)
    (hγ : γ ≠ -ρ) :
    ∃ P₀ P₁ : K[X], P₀.natDegree < k ∧ P₁.natDegree < k ∧
      (∀ x ∈ T, P₀.eval x = Y₀.eval x) ∧
      (∀ x ∈ T, P₁.eval x = Y₁.eval x) := by
  have hn : ρ + γ ≠ 0 := by
    intro h
    apply hγ
    linear_combination h
  let P₁ : K[X] := (ρ + γ)⁻¹ • (P - C)
  let P₀ : K[X] := C + ρ • P₁
  have hd₁ : P₁.natDegree < k :=
    (natDegree_smul_le _ _).trans_lt
      ((natDegree_sub_le _ _).trans_lt (max_lt hP hC))
  have hd₀ : P₀.natDegree < k :=
    (natDegree_add_le _ _).trans_lt
      (max_lt hC ((natDegree_smul_le _ _).trans_lt hd₁))
  have he₁ : ∀ x ∈ T, P₁.eval x = Y₁.eval x := by
    intro x hx
    dsimp [P₁]
    rw [eval_smul, eval_sub, hfit x hx, hglobal x (hTS hx)]
    simp only [smul_eq_mul]
    field_simp
    ring
  refine ⟨P₀, P₁, hd₀, hd₁, ?_, he₁⟩
  intro x hx
  dsimp [P₀]
  rw [eval_add, eval_smul, he₁ x hx, hglobal x (hTS hx)]
  simp

/-- If the second word is globally coded, every fitted combination fits both words. -/
theorem simultaneous_fit_of_second_word_code
    (S T : Finset K) (hTS : T ⊆ S) (Y₀ Y₁ C P : K[X]) (γ : K) {k : ℕ}
    (hC : C.natDegree < k) (hP : P.natDegree < k)
    (hglobal : ∀ x ∈ S, C.eval x = Y₁.eval x)
    (hfit : ∀ x ∈ T, P.eval x = Y₀.eval x + γ * Y₁.eval x) :
    ∃ P₀ P₁ : K[X], P₀.natDegree < k ∧ P₁.natDegree < k ∧
      (∀ x ∈ T, P₀.eval x = Y₀.eval x) ∧
      (∀ x ∈ T, P₁.eval x = Y₁.eval x) := by
  refine ⟨P - γ • C, C, ?_, hC, ?_, fun x hx => hglobal x (hTS hx)⟩
  · exact (natDegree_sub_le _ _).trans_lt
      (max_lt hP ((natDegree_smul_le _ _).trans_lt hC))
  · intro x hx
    rw [eval_sub, eval_smul, hfit x hx, hglobal x (hTS hx)]
    simp

/-- A same-support nonfit under a global affine relation forces the unique parameter. -/
theorem parameter_eq_neg_of_dependent_word
    (S T : Finset K) (hTS : T ⊆ S) (Y₀ Y₁ C P : K[X]) (ρ γ : K) {k : ℕ}
    (hC : C.natDegree < k) (hP : P.natDegree < k)
    (hglobal : ∀ x ∈ S, C.eval x = Y₀.eval x - ρ * Y₁.eval x)
    (hfit : ∀ x ∈ T, P.eval x = Y₀.eval x + γ * Y₁.eval x)
    (hnonfit : ¬ ∃ P₀ P₁ : K[X], P₀.natDegree < k ∧ P₁.natDegree < k ∧
      (∀ x ∈ T, P₀.eval x = Y₀.eval x) ∧
      (∀ x ∈ T, P₁.eval x = Y₁.eval x)) : γ = -ρ := by
  by_contra hγ
  exact hnonfit (simultaneous_fit_of_dependent_word S T hTS Y₀ Y₁ C P ρ γ
    hC hP hglobal hfit hγ)

/-- Supports and candidate polynomials may vary with the parameter. -/
theorem dependent_parameters_subsingleton
    (S : Finset K) (Y₀ Y₁ C : K[X]) (ρ : K) {k : ℕ}
    (hC : C.natDegree < k)
    (hglobal : ∀ x ∈ S, C.eval x = Y₀.eval x - ρ * Y₁.eval x)
    (Γ : Set K)
    (hΓ : ∀ γ ∈ Γ, ∃ T : Finset K, T ⊆ S ∧ ∃ P : K[X],
      P.natDegree < k ∧ (∀ x ∈ T, P.eval x = Y₀.eval x + γ * Y₁.eval x) ∧
      ¬ ∃ P₀ P₁ : K[X], P₀.natDegree < k ∧ P₁.natDegree < k ∧
        (∀ x ∈ T, P₀.eval x = Y₀.eval x) ∧
        (∀ x ∈ T, P₁.eval x = Y₁.eval x)) : Γ.Subsingleton := by
  have heq : ∀ γ ∈ Γ, γ = -ρ := by
    intro γ hγ
    obtain ⟨T, hTS, P, hP, hfit, hnonfit⟩ := hΓ γ hγ
    exact parameter_eq_neg_of_dependent_word S T hTS Y₀ Y₁ C P ρ γ
      hC hP hglobal hfit hnonfit
  intro γ hγ δ hδ
  exact (heq γ hγ).trans (heq δ hδ).symm

theorem dependent_parameters_card_le_one
    (S : Finset K) (Y₀ Y₁ C : K[X]) (ρ : K) {k : ℕ}
    (hC : C.natDegree < k)
    (hglobal : ∀ x ∈ S, C.eval x = Y₀.eval x - ρ * Y₁.eval x)
    (Γ : Finset K)
    (hΓ : ∀ γ ∈ Γ, ∃ T : Finset K, T ⊆ S ∧ ∃ P : K[X],
      P.natDegree < k ∧ (∀ x ∈ T, P.eval x = Y₀.eval x + γ * Y₁.eval x) ∧
      ¬ ∃ P₀ P₁ : K[X], P₀.natDegree < k ∧ P₁.natDegree < k ∧
        (∀ x ∈ T, P₀.eval x = Y₀.eval x) ∧
        (∀ x ∈ T, P₁.eval x = Y₁.eval x)) : Γ.card ≤ 1 := by
  apply Finset.card_le_one_iff_subsingleton.mpr
  exact dependent_parameters_subsingleton S Y₀ Y₁ C ρ hC hglobal (Γ : Set K) hΓ


end
end ProximityPadeDependentCase


namespace ProximityPadeVectorDichotomy

variable {K I : Type*} [Field K]

/-- A pair of vectors either has a nonzero two-coordinate minor or is dependent. -/
theorem minor_or_zero_or_smul (A B : I → K) :
    (∃ j l, A j * B l - B j * A l ≠ 0) ∨
      B = 0 ∨ ∃ ρ : K, A = ρ • B := by
  classical
  by_cases hm : ∃ j l, A j * B l - B j * A l ≠ 0
  · exact Or.inl hm
  right
  by_cases hB : B = 0
  · exact Or.inl hB
  right
  have hn : ∃ j, B j ≠ 0 := by
    by_contra h
    apply hB
    funext j
    by_contra hj
    exact h ⟨j, hj⟩
  obtain ⟨j, hj⟩ := hn
  refine ⟨A j / B j, ?_⟩
  funext l
  change A l = (A j / B j) * B l
  have hml : A j * B l - B j * A l = 0 := by
    by_contra h
    exact hm ⟨j, l, h⟩
  field_simp
  linear_combination -hml


end ProximityPadeVectorDichotomy


namespace ProximityPadeProjectiveSubline

variable {F K ι : Type*} [Field F] [Field K]

/-- A nondegenerate fractional linear function is injective away from its pole.
The elementary cross-product proof follows the existing FractionalKey scratch lemma. -/
theorem fractional_injective_off_pole (a b c d : K)
    (hdet : a * d - b * c ≠ 0) :
    Set.InjOn (fun γ : K => (a + γ * b) / (c + γ * d))
      {γ : K | c + γ * d ≠ 0} := by
  intro x hx y hy hxy
  have hcross : (a + x * b) * (c + y * d) = (a + y * b) * (c + x * d) :=
    (div_eq_div_iff hx hy).mp hxy
  have hz : (x - y) * (a * d - b * c) = 0 := by
    calc
      (x - y) * (a * d - b * c) =
          (a + y * b) * (c + x * d) - (a + x * b) * (c + y * d) := by ring
      _ = 0 := sub_eq_zero.mpr hcross.symm
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hdet)

/-- Parameters whose nondegenerate coordinate ratio lies in a finite subfield are bounded
by the cardinality of that subfield, provided the denominator is nonzero. -/
theorem card_le_of_fractional_mem_subfield [Fintype F]
    (i : F →+* K) (Γ : Finset K) (a b c d : K)
    (hdet : a * d - b * c ≠ 0)
    (hpole : ∀ γ ∈ Γ, c + γ * d ≠ 0)
    (hbase : ∀ γ ∈ Γ, ∃ z : F, (a + γ * b) / (c + γ * d) = i z) :
    Γ.card ≤ Fintype.card F := by
  classical
  let f : K → K := fun γ => (a + γ * b) / (c + γ * d)
  have hinj : Set.InjOn f (Γ : Set K) := by
    intro x hx y hy hxy
    exact fractional_injective_off_pole a b c d hdet
      (hpole x hx) (hpole y hy) hxy
  have hsub : Γ.image f ⊆ (Finset.univ : Finset F).image i := by
    intro z hz
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨u, hu⟩ := hbase γ hγ
    exact Finset.mem_image.mpr ⟨u, Finset.mem_univ _, hu.symm⟩
  calc
    Γ.card = (Γ.image f).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ ((Finset.univ : Finset F).image i).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset F).card := Finset.card_image_le
    _ = Fintype.card F := Finset.card_univ

/-- A nonzero two-coordinate determinant permits at most one denominator pole. -/
theorem pole_subsingleton (a b c d : K) (hdet : a * d - b * c ≠ 0)
    {x y : K} (hx : c + x * d = 0) (hy : c + y * d = 0) : x = y := by
  have hd : d ≠ 0 := by
    intro hd
    have hc : c = 0 := by simpa only [hd, mul_zero, add_zero] using hx
    exact hdet (by simp [hd, hc])
  have hz : (x - y) * d = 0 := by linear_combination hx - hy
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hd)

/-- A projective subfield condition on two nondegenerate affine coordinates bounds the
number of affine parameters by the size of the projective subfield line. -/
theorem card_le_subfield_card_add_one_of_pair [Fintype F]
    (i : F →+* K) (Γ : Finset K) (a b c d : K)
    (hdet : a * d - b * c ≠ 0)
    (hprojective : ∀ γ ∈ Γ, ∃ η : K, η ≠ 0 ∧ ∃ u v : F,
      a + γ * b = η * i u ∧ c + γ * d = η * i v) :
    Γ.card ≤ Fintype.card F + 1 := by
  classical
  let regular := Γ.filter fun γ => c + γ * d ≠ 0
  let poles := Γ.filter fun γ => c + γ * d = 0
  have hregular : regular.card ≤ Fintype.card F := by
    apply card_le_of_fractional_mem_subfield i regular a b c d hdet
    · intro γ hγ
      exact (Finset.mem_filter.mp hγ).2
    · intro γ hγ
      obtain ⟨η, hη, u, v, hu, hv⟩ := hprojective γ (Finset.mem_filter.mp hγ).1
      refine ⟨u / v, ?_⟩
      rw [hu, hv, map_div₀]
      exact mul_div_mul_left (i u) (i v) hη
  have hpoles : poles.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    exact pole_subsingleton a b c d hdet
      (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2
  have hpartition : regular.card + poles.card = Γ.card := by
    simpa only [regular, poles, not_not] using
      (Finset.card_filter_add_card_filter_not (s := Γ) (fun γ => c + γ * d ≠ 0))
  calc
    Γ.card = regular.card + poles.card := hpartition.symm
    _ ≤ Fintype.card F + 1 := Nat.add_le_add hregular hpoles

/-- A line with two independent coordinate pivots has at most `|F|+1` parameters for which
its vector is a nonzero scalar multiple of an embedded `F`-vector. -/
theorem projective_subfield_line_card_le [Fintype F]
    (i : F →+* K) (Γ : Finset K) (A B : ι → K) (j l : ι)
    (hdet : A j * B l - B j * A l ≠ 0)
    (hprojective : ∀ γ ∈ Γ, ∃ η : K, η ≠ 0 ∧ ∃ v : ι → F,
      ∀ x, A x + γ * B x = η * i (v x)) :
    Γ.card ≤ Fintype.card F + 1 := by
  apply card_le_subfield_card_add_one_of_pair i Γ (A j) (B j) (A l) (B l) hdet
  intro γ hγ
  obtain ⟨η, hη, v, hv⟩ := hprojective γ hγ
  exact ⟨η, hη, v j, v l, hv j, hv l⟩

end ProximityPadeProjectiveSubline



namespace ProximityPadeErrorLineCount

noncomputable section
open Polynomial
open ProximityPadeParity

variable {K : Type*} [Field K]

/-- Same-support MCA parameters with whole-domain prime-field error lines are at most p+1.
The support and candidate polynomial may differ for every parameter. -/
theorem mca_error_line_card_le (p : ℕ) [Fact p.Prime] [CharP K p]
    (S : Finset K) (k : ℕ) (hk : 0<k) (hkS : k≤S.card)
    (hS : ∀ x∈S, x^p=x) (Y₀ Y₁ : K[X]) (Γ : Finset K)
    (hΓ : ∀ γ∈Γ, ∃ T : Finset K, T⊆S ∧ ∃ P : K[X],
      P.natDegree<k ∧ (∀ x∈T, P.eval x=Y₀.eval x+γ*Y₁.eval x) ∧
      (¬∃ P₀ P₁ : K[X], P₀.natDegree<k ∧ P₁.natDegree<k ∧
        (∀ x∈T, P₀.eval x=Y₀.eval x) ∧ (∀ x∈T, P₁.eval x=Y₁.eval x)) ∧
      ∃ η : K, η≠0 ∧ ∀ x∈S,
        (Y₀.eval x+γ*Y₁.eval x-P.eval x)/η ∈ (⊥ : Subfield K)) :
    Γ.card≤p+1 := by
  classical
  let A := parity S k Y₀
  let B := parity S k Y₁
  have hmca : ∀ γ∈Γ, ∃ T : Finset K, T⊆S ∧ ∃ P : K[X],
      P.natDegree<k ∧ (∀ x∈T, P.eval x=Y₀.eval x+γ*Y₁.eval x) ∧
      ¬∃ P₀ P₁ : K[X], P₀.natDegree<k ∧ P₁.natDegree<k ∧
        (∀ x∈T, P₀.eval x=Y₀.eval x) ∧ (∀ x∈T, P₁.eval x=Y₁.eval x) := by
    intro γ hγ
    obtain ⟨T,hTS,P,hP,hfit,hnot,_⟩ := hΓ γ hγ
    exact ⟨T,hTS,P,hP,hfit,hnot⟩
  rcases ProximityPadeVectorDichotomy.minor_or_zero_or_smul A B with
    ⟨j,l,hdet⟩ | hB | ⟨ρ,hdep⟩
  · letI := Subfield.fintypeBot K p
    have hprojective : ∀ γ∈Γ, ∃ η : K, η≠0 ∧
        ∃ v : Fin (S.card-k) → (⊥ : Subfield K),
          ∀ i, A i+γ*B i=η*(v i : K) := by
      intro γ hγ
      obtain ⟨T,hTS,P,hP,hfit,hnot,η,hη,hline⟩ := hΓ γ hγ
      obtain ⟨v,hv⟩ := parity_error_line p S k hk hkS hS (Y₀+γ • Y₁) P hP η hη
        (by simpa only [Polynomial.eval_add, Polynomial.eval_smul, smul_eq_mul] using hline)
      refine ⟨η,hη,v,?_⟩
      intro i
      have hi := hv i
      rw [parity_affine] at hi
      simpa only [A,B,Pi.add_apply,Pi.smul_apply,smul_eq_mul] using hi
    have hc := ProximityPadeProjectiveSubline.projective_subfield_line_card_le
      (Subfield.subtype (⊥ : Subfield K)) Γ A B j l hdet hprojective
    simpa only [Fintype.card_eq_nat_card, Subfield.card_bot K p] using hc
  · obtain ⟨C,hC,hglobal⟩ := (parity_zero_iff S k hk hkS Y₁).1 hB
    have hempty : Γ=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro γ hγ
      obtain ⟨T,hTS,P,hP,hfit,hnot⟩ := hmca γ hγ
      exact hnot (ProximityPadeDependentCase.simultaneous_fit_of_second_word_code
        S T hTS Y₀ Y₁ C P γ hC hP (fun x hx => (hglobal x hx).symm) hfit)
    simp only [hempty,Finset.card_empty,Nat.zero_le]
  · have hz : parity S k (Y₀-ρ • Y₁)=0 := by
      rw [parity_sub,parity_smul]
      exact sub_eq_zero.mpr hdep
    obtain ⟨C,hC,hglobal⟩ := (parity_zero_iff S k hk hkS _).1 hz
    have hc := ProximityPadeDependentCase.dependent_parameters_card_le_one
      S Y₀ Y₁ C ρ hC
      (fun x hx => by simpa only [Polynomial.eval_sub,Polynomial.eval_smul,smul_eq_mul]
        using (hglobal x hx).symm) Γ hmca
    omega

/-- The all-zero error outcome from the forward bridge is covered by choosing scale one. -/
theorem mca_error_line_or_zero_card_le (p : ℕ) [Fact p.Prime] [CharP K p]
    (S : Finset K) (k : ℕ) (hk : 0<k) (hkS : k≤S.card)
    (hS : ∀ x∈S, x^p=x) (Y₀ Y₁ : K[X]) (Γ : Finset K)
    (hΓ : ∀ γ∈Γ, ∃ T : Finset K, T⊆S ∧ ∃ P : K[X],
      P.natDegree<k ∧ (∀ x∈T, P.eval x=Y₀.eval x+γ*Y₁.eval x) ∧
      (¬∃ P₀ P₁ : K[X], P₀.natDegree<k ∧ P₁.natDegree<k ∧
        (∀ x∈T, P₀.eval x=Y₀.eval x) ∧ (∀ x∈T, P₁.eval x=Y₁.eval x)) ∧
      ((∀ x∈S, Y₀.eval x+γ*Y₁.eval x-P.eval x=0) ∨
        ∃ η : K, η≠0 ∧ ∀ x∈S,
          (Y₀.eval x+γ*Y₁.eval x-P.eval x)/η ∈ (⊥ : Subfield K))) :
    Γ.card≤p+1 := by
  apply mca_error_line_card_le p S k hk hkS hS Y₀ Y₁ Γ
  intro γ hγ
  obtain ⟨T,hTS,P,hP,hfit,hnot,hline⟩ := hΓ γ hγ
  refine ⟨T,hTS,P,hP,hfit,hnot,?_⟩
  rcases hline with hz | hline
  · refine ⟨1,one_ne_zero,?_⟩
    intro x hx
    simp only [hz x hx,zero_div,zero_mem]
  · exact hline


end
end ProximityPadeErrorLineCount



open Polynomial ProximityPadeErrorLineCount

theorem solution {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (S : Finset K) (k : ℕ) (hk : 0<k) (hkS : k≤S.card)
    (hS : ∀ x∈S, x^p=x) (Y₀ Y₁ : K[X]) (Γ : Finset K)
    (hΓ : ∀ γ∈Γ, ∃ T : Finset K, T⊆S ∧ ∃ P : K[X],
      P.natDegree<k ∧ (∀ x∈T, P.eval x=Y₀.eval x+γ*Y₁.eval x) ∧
      (¬∃ P₀ P₁ : K[X], P₀.natDegree<k ∧ P₁.natDegree<k ∧
        (∀ x∈T, P₀.eval x=Y₀.eval x) ∧ (∀ x∈T, P₁.eval x=Y₁.eval x)) ∧
      ∃ η : K, ∃ v : K → (⊥ : Subfield K), ∀ x∈S,
        Y₀.eval x+γ*Y₁.eval x-P.eval x=η*(v x : K)) :
    Γ.card≤p+1 := by
  apply mca_error_line_or_zero_card_le p S k hk hkS hS Y₀ Y₁ Γ
  intro γ hγ
  obtain ⟨T,hTS,P,hP,hfit,hnot,η,v,hline⟩ := hΓ γ hγ
  refine ⟨T,hTS,P,hP,hfit,hnot,?_⟩
  by_cases hη : η=0
  · left
    intro x hx
    simpa only [hη,zero_mul] using hline x hx
  · right
    refine ⟨η,hη,?_⟩
    intro x hx
    rw [hline x hx]
    have heq : η*(v x : K)/η=(v x : K) := by field_simp
    rw [heq]
    exact (v x).property

