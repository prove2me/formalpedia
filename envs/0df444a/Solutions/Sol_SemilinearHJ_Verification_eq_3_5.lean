-- Prove2me | solution 1 for SemilinearHJ.Verification.eq_3_5
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T06:04:40.398717+00:00
-- url     : https://prove2.me/submissions/8ebef989-a85c-498e-bc13-1f47d8006c84

import Mathlib
import Definitions.Def_SemilinearHJ_Verification_Setting

open scoped ENNReal MeasureTheory
open SemilinearHJ.Verification

namespace M31

lemma inner_eq {n : ℕ} (u v : E n) : inner ℝ u v = ∑ i, u i * v i := by
  simp [PiLp.inner_apply, mul_comm]

lemma l1_nonneg {n : ℕ} (v : E n) : 0 ≤ l1 v := Finset.sum_nonneg fun i _ => abs_nonneg _

lemma abs_le_l1 {n : ℕ} (v : E n) (i : Fin n) : |v i| ≤ l1 v :=
  Finset.single_le_sum (f := fun i => |v i|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)

lemma l1_smul {n : ℕ} (c : ℝ) (v : E n) : l1 (c • v) = |c| * l1 v := by
  simp [l1, abs_mul, Finset.mul_sum]

lemma continuous_l1 {n : ℕ} : Continuous (fun v : E n => l1 v) := by
  unfold l1; fun_prop

lemma isCompact_of_poly {n : ℕ} {X : Set (E n)} (hX : IsPolytope X) : IsCompact X := by
  obtain ⟨S, -, rfl⟩ := hX
  exact S.finite_toSet.isCompact_convexHull ℝ

lemma convex_of_poly {n : ℕ} {X : Set (E n)} (hX : IsPolytope X) : Convex ℝ X := by
  obtain ⟨S, -, rfl⟩ := hX
  exact convex_convexHull ℝ _

lemma bdd_psi {n : ℕ} {X : Set (E n)} (hX : IsPolytope X) (Ψ : E n → E n)
    (hΨL : ∃ K : NNReal, LipschitzOnWith K Ψ X) : BddAbove ((fun x => l1 (Ψ x)) '' X) := by
  obtain ⟨K, hK⟩ := hΨL
  exact ((isCompact_of_poly hX).image_of_continuousOn
    (continuous_l1.comp_continuousOn hK.continuousOn)).bddAbove

lemma l1_le_psiNorm {n : ℕ} {X : Set (E n)} (hX : IsPolytope X) (Ψ : E n → E n)
    (hΨL : ∃ K : NNReal, LipschitzOnWith K Ψ X) {x : E n} (hx : x ∈ X) :
    l1 (Ψ x) ≤ psiNorm X Ψ :=
  le_csSup (bdd_psi hX Ψ hΨL) ⟨x, hx, rfl⟩

lemma psiNorm_nonneg {n : ℕ} (X : Set (E n)) (Ψ : E n → E n) : 0 ≤ psiNorm X Ψ := by
  apply Real.sSup_nonneg
  rintro _ ⟨x, -, rfl⟩
  exact l1_nonneg _

/-- the cost integrand bound -/
lemma cost_le {n : ℕ} {X : Set (E n)} (hX : IsPolytope X) (Ψ : E n → E n)
    (hΨL : ∃ K : NNReal, LipschitzOnWith K Ψ X) (hΨ0 : ∀ x ∈ X, ∀ i, 0 ≤ Ψ x i)
    {x : E n} (hx : x ∈ X) (v : E n) :
    ∑ i, Ψ x i * max (v i) 0 ≤ psiNorm X Ψ * l1 v := by
  calc ∑ i, Ψ x i * max (v i) 0 ≤ ∑ i, |Ψ x i| * l1 v := by
        apply Finset.sum_le_sum; intro i _
        rw [abs_of_nonneg (hΨ0 x hx i)]
        apply mul_le_mul_of_nonneg_left _ (hΨ0 x hx i)
        exact max_le ((le_abs_self _).trans (abs_le_l1 v i)) (l1_nonneg v)
    _ = l1 (Ψ x) * l1 v := by rw [l1, ← Finset.sum_mul]; rfl
    _ ≤ psiNorm X Ψ * l1 v := mul_le_mul_of_nonneg_right (l1_le_psiNorm hX Ψ hΨL hx) (l1_nonneg v)

lemma zero_mem_ballR {n : ℕ} (X : Set (E n)) {r : ℝ} (hr : 0 ≤ r) : (0 : E n) ∈ ballR X r :=
  ⟨Submodule.zero_mem _, by simp [l1, hr]⟩

lemma ham_bdd {n : ℕ} (X : Set (E n)) (Ψ : E n → E n) (r : ℝ) {x : E n}
    (hΨ0 : ∀ i, 0 ≤ Ψ x i) (u : E n) :
    BddAbove ((fun v => inner ℝ u v - ∑ i, Ψ x i * max (v i) 0) '' ballR X r) := by
  refine ⟨l1 u * r, ?_⟩
  rintro _ ⟨v, hv, rfl⟩
  have h1 : 0 ≤ ∑ i, Ψ x i * max (v i) 0 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hΨ0 i) (le_max_right _ _)
  have h2 : inner ℝ u v ≤ l1 u * r := by
    rw [inner_eq, l1, Finset.sum_mul]
    apply Finset.sum_le_sum; intro i _
    calc u i * v i ≤ |u i| * |v i| := by rw [← abs_mul]; exact le_abs_self _
      _ ≤ |u i| * r := mul_le_mul_of_nonneg_left ((abs_le_l1 v i).trans hv.2) (abs_nonneg _)
  linarith

lemma le_ham {n : ℕ} (X : Set (E n)) (Ψ : E n → E n) (r : ℝ) {x : E n}
    (hΨ0 : ∀ i, 0 ≤ Ψ x i) (u v : E n) (hv : v ∈ ballR X r) :
    inner ℝ u v - ∑ i, Ψ x i * max (v i) 0 ≤ ham X Ψ r x u :=
  le_csSup (ham_bdd X Ψ r hΨ0 u) ⟨v, hv, rfl⟩

lemma ham_nonneg {n : ℕ} (X : Set (E n)) (Ψ : E n → E n) {r : ℝ} (hr : 0 ≤ r) {x : E n}
    (hΨ0 : ∀ i, 0 ≤ Ψ x i) (u : E n) : 0 ≤ ham X Ψ r x u := by
  have := le_ham X Ψ r hΨ0 u 0 (zero_mem_ballR X hr)
  simpa using this

end M31

open M31

theorem solution {n : ℕ} (X : Set (E n)) (hX : IsPolytope X)
    (Ψ : E n → E n) (hΨL : ∃ K : NNReal, LipschitzOnWith K Ψ X) (hΨ0 : ∀ x ∈ X, ∀ i, 0 ≤ Ψ x i)
    (r : ℝ) (hr : 0 < r) :
    ∀ x ∈ X, ∀ u ∈ vectorSpan ℝ X, r / n * l1 u - r * psiNorm X Ψ ≤ ham X Ψ r x u := by
  intro x hx u hu
  have hP := psiNorm_nonneg X Ψ
  rcases (l1_nonneg u).eq_or_lt with h0 | hpos
  · rw [← h0]
    have := ham_nonneg X Ψ hr.le (hΨ0 x hx) u
    nlinarith
  · set v : E n := (r / l1 u) • u with hvdef
    have hl1v : l1 v = r := by
      rw [hvdef, l1_smul, abs_of_nonneg (div_nonneg hr.le (l1_nonneg u))]
      field_simp
    have hv : v ∈ ballR X r := ⟨Submodule.smul_mem _ _ hu, hl1v.le⟩
    have h1 := le_ham X Ψ r (hΨ0 x hx) u v hv
    have h2 := cost_le hX Ψ hΨL hΨ0 hx v
    rw [hl1v] at h2
    have hn : (0 : ℝ) < n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp [l1] at hpos
      · exact_mod_cast h
    have hcs : (l1 u) ^ 2 ≤ n * ∑ i, u i ^ 2 := by
      have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1:ℝ)) (fun i => |u i|)
      simpa [l1, sq_abs] using this
    have hin : inner ℝ u v = r / l1 u * ∑ i, u i ^ 2 := by
      rw [hvdef, inner_eq, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i _
      simp [PiLp.smul_apply]; ring
    have h3 : r / n * l1 u ≤ r / l1 u * ∑ i, u i ^ 2 := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff₀ hn hpos]
      nlinarith
    linarith

