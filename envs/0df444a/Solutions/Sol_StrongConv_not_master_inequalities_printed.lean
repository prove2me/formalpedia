-- Prove2me | solution 1 for StrongConv.not_master_inequalities_printed
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-04T23:25:31.577262+00:00
-- url     : https://prove2.me/submissions/778ffdac-675e-4664-a147-60fd2840cc6d

import Mathlib
import Definitions.Def_StrongConv

open Filter Topology Polynomial

namespace StrongConv

noncomputable def cP : NCPoly 1 0 := Finsupp.single 1 1

lemma wordStar_one : NCPoly.wordStar (d := 0) 1 = 1 := by
  simp [NCPoly.wordStar]

lemma wordStar_eq_one {d : ℕ} (w : FreeMonoid (Fin d ⊕ Fin d)) : NCPoly.wordStar w = 1 ↔ w = 1 := by
  unfold NCPoly.wordStar
  constructor
  · intro h
    have := congrArg FreeMonoid.length h
    simp [FreeMonoid.length] at this
    exact FreeMonoid.length_eq_zero.mp (by simpa [FreeMonoid.length] using this)
  · rintro rfl; rfl

lemma cP_selfAdjoint : cP.IsSelfAdjoint := by
  intro w
  by_cases hw : w = 1
  · subst hw; simp [cP, wordStar_one]
  · have : NCPoly.wordStar w ≠ 1 := fun h => hw ((wordStar_eq_one w).mp h)
    simp [cP, Finsupp.single_apply, hw, this]

lemma cP_degree : cP.degree = 0 := by
  simp [NCPoly.degree, cP, Finsupp.support_single_ne_zero _ one_ne_zero]

lemma eval_cP {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (u : Fin 0 → H →L[ℂ] H) : cP.eval u = 1 := by
  classical
  simp only [NCPoly.eval, cP]
  rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, Finsupp.single_eq_same]
  simp only [wordOp, FreeMonoid.toList_one, List.map_nil, List.prod_nil, tensorOp]
  ext x i
  simp [Fin.sum_univ_succ, Matrix.one_apply]
  fin_cases i; simp

lemma finrank_onesPerp {N : ℕ} (hN : 1 ≤ N) : Module.finrank ℂ (OnesPerp N) = N - 1 := by
  have h1 := Submodule.finrank_add_finrank_orthogonal (ℂ ∙ onesVec N)
  have hne : onesVec N ≠ 0 := by
    intro h
    have := congrFun (congrArg WithLp.ofLp h) ⟨0, hN⟩
    simp [onesVec] at this
  rw [finrank_span_singleton hne] at h1
  simp only [finrank_euclideanSpace, Fintype.card_fin] at h1
  unfold OnesPerp
  omega

lemma trDN_one {N : ℕ} (hN : 1 ≤ N) :
    trDN 1 N 1 = ((N : ℝ) - 1) / N := by
  unfold trDN
  have : Module.finrank ℂ (PiLp 2 (fun _ : Fin 1 => OnesPerp N)) = N - 1 := by
    rw [← finrank_onesPerp hN]
    rw [(WithLp.linearEquiv 2 ℂ (Fin 1 → OnesPerp N)).finrank_eq]
    rw [Module.finrank_pi_fintype]; simp
  have h2 : (LinearMap.trace ℂ _ (((1 : PiLp 2 (fun _ : Fin 1 => OnesPerp N) →L[ℂ]
      PiLp 2 (fun _ : Fin 1 => OnesPerp N))) : PiLp 2 (fun _ : Fin 1 => OnesPerp N) →ₗ[ℂ]
      PiLp 2 (fun _ : Fin 1 => OnesPerp N))).re = ((N : ℝ) - 1) := by
    have : ((1 : PiLp 2 (fun _ : Fin 1 => OnesPerp N) →L[ℂ]
      PiLp 2 (fun _ : Fin 1 => OnesPerp N)) : PiLp 2 (fun _ : Fin 1 => OnesPerp N) →ₗ[ℂ]
      PiLp 2 (fun _ : Fin 1 => OnesPerp N)) = LinearMap.id := rfl
    rw [this, LinearMap.trace_id, ‹Module.finrank ℂ _ = N - 1›]
    rw [Nat.cast_sub hN]; simp
  rw [h2]; simp

lemma expTr_cP {N : ℕ} (hN : 1 ≤ N) : expTr cP N (fun _ => 1) = ((N : ℝ) - 1) / N := by
  unfold expTr uniformExp
  have : ∀ σ : Fin 0 → Equiv.Perm (Fin N),
      trDN 1 N (fnCalc (fun _ : ℝ => (1 : ℝ)) (cP.eval (sModel σ))) = ((N : ℝ) - 1) / N := by
    intro σ
    rw [eval_cP, ← trDN_one hN]
    congr 1
    unfold fnCalc
    simp
  simp [this]

theorem not_master_dev :
    ¬ ∀ {D d q₀ : ℕ} (P : NCPoly D d), P.IsSelfAdjoint → P.degree ≤ q₀ →
      ∃ ν : ℕ → ℝ[X] →ₗ[ℝ] ℝ, ∀ N m q : ℕ, 1 ≤ N → 1 ≤ m → 1 ≤ q → ∀ h : ℝ[X], h.natDegree ≤ q →
        |expTr P N (fun x => h.eval x) - ∑ i ∈ Finset.range m, ν i h / (N : ℝ) ^ i| ≤
          (4 * q * q₀ * (1 + Real.log d)) ^ (4 * m) / (N : ℝ) ^ m *
            cNorm 0 (fun x => h.eval x) (-P.fullNorm) P.fullNorm := by
  intro H
  obtain ⟨ν, hν⟩ := H (q₀ := 0) cP cP_selfAdjoint (by rw [cP_degree])
  have key : ∀ N : ℕ, 1 ≤ N → expTr cP N (fun _ => 1) = ν 0 1 := by
    intro N hN
    have := hν N 1 1 hN le_rfl le_rfl 1 (by simp)
    simp only [Polynomial.eval_one] at this
    simp at this
    linarith
  have h1 := key 1 le_rfl
  have h2 := key 2 (by norm_num)
  rw [expTr_cP le_rfl] at h1
  rw [expTr_cP (by norm_num)] at h2
  norm_num at h1 h2
  linarith

end StrongConv

theorem solution : type_of% @StrongConv.not_master_dev := @StrongConv.not_master_dev
