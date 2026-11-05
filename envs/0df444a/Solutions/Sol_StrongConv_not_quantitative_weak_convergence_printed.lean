-- Prove2me | solution 1 for StrongConv.not_quantitative_weak_convergence_printed
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-04T23:25:31.55922+00:00
-- url     : https://prove2.me/submissions/8527fc40-5910-45dc-bab4-49270e975b9a

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

lemma trTau_cP : trTau (cP.eval (sLimit 0)) = 1 := by
  rw [eval_cP]
  unfold trTau
  simp [delta]


theorem not_quant_dev :
    ¬ ∃ C : ℝ, ∀ {D d q₀ : ℕ} (P : NCPoly D d), P.IsSelfAdjoint → P.degree ≤ q₀ → 1 ≤ q₀ →
      ∀ N : ℕ, 1 ≤ N → ∀ β : ℝ, 1 < β → ∀ h : smoothFun,
        ‖(expTr P N (h : ℝ → ℝ) : ℂ) - trTau (fnCalc (h : ℝ → ℝ) (P.eval (sLimit d)))‖ ≤
          C * (q₀ * (1 + Real.log d)) ^ 4 / N * conjExp β *
            lpNormCircle β (iteratedDeriv 5 (fun θ => (h : ℝ → ℝ) (P.fullNorm * Real.cos θ))) := by
  rintro ⟨C, H⟩
  let one : smoothFun := ⟨fun _ => 1, (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) fun _ : ℝ => (1 : ℝ))⟩
  have := H (q₀ := 1) cP cP_selfAdjoint (by rw [cP_degree]; norm_num) le_rfl 1 le_rfl 2
    (by norm_num) one
  have hf : fnCalc (fun _ : ℝ => (1 : ℝ)) (cP.eval (sLimit 0)) = 1 := by
    rw [eval_cP]; unfold fnCalc; simp
  change ‖(expTr cP 1 (fun _ => 1) : ℂ) - trTau (fnCalc (fun _ : ℝ => (1 : ℝ)) (cP.eval (sLimit 0)))‖
    ≤ _ at this
  have hd : iteratedDeriv 5 (fun θ => (fun _ : ℝ => (1 : ℝ)) (cP.fullNorm * Real.cos θ)) = 0 := by
    funext x
    simp [iteratedDeriv_eq_iterate]
  change _ ≤ C * (((1 : ℕ) : ℝ) * (1 + Real.log ((0 : ℕ) : ℝ))) ^ 4 / ((1 : ℕ) : ℝ) * conjExp 2 *
    lpNormCircle 2 (iteratedDeriv 5 (fun θ => (fun _ : ℝ => (1 : ℝ)) (cP.fullNorm * Real.cos θ))) at this
  rw [hf, hd, expTr_cP le_rfl] at this
  have h0 : lpNormCircle 2 (0 : ℝ → ℝ) = 0 := by
    unfold lpNormCircle; simp
  rw [h0] at this
  have : trTau (1 : PiLp 2 (fun _ : Fin 1 => L2Free 0) →L[ℂ] PiLp 2 (fun _ : Fin 1 => L2Free 0)) = 1 := by
    rw [← eval_cP (fun i : Fin 0 => sLimit 0 i)]; exact trTau_cP
  simp_all
  norm_num at *

end StrongConv

theorem solution : type_of% @StrongConv.not_quant_dev := @StrongConv.not_quant_dev
