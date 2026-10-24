-- Prove2me | solution 1 for SKAlgorithm.Qudit.recursion_invariant
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T07:49:19.844209+00:00
-- url     : https://prove2.me/submissions/6a3cd0fe-de82-4290-9635-53e9daf8b53e

import Mathlib
import Definitions.Def_SKAlgorithm_Qudit_Model
import Theorems.Thm_SKAlgorithm_Qudit_lemma_1

open scoped Matrix Matrix.Norms.L2Operator
open QAlgorithms

namespace SKAlgorithm.Qudit.RecursionProof

variable {d : ℕ}

lemma opDist_symm (U V : SU d) : opDist U V = opDist V U := norm_sub_rev _ _

lemma opDist_triangle (U V W : SU d) : opDist U W ≤ opDist U V + opDist V W := by
  change ‖(U : Matrix (Fin d) (Fin d) ℂ) - (W : Matrix (Fin d) (Fin d) ℂ)‖ ≤ _
  simpa only [opDist, specNorm, sub_add_sub_cancel] using norm_add_le
    ((U : Matrix (Fin d) (Fin d) ℂ) - (V : Matrix (Fin d) (Fin d) ℂ))
    ((V : Matrix (Fin d) (Fin d) ℂ) - (W : Matrix (Fin d) (Fin d) ℂ))

lemma opDist_mul_right (U V W : SU d) : opDist (U * W) (V * W) = opDist U V := by
  change ‖(U : Matrix (Fin d) (Fin d) ℂ) * (W : Matrix (Fin d) (Fin d) ℂ) -
    (V : Matrix (Fin d) (Fin d) ℂ) * (W : Matrix (Fin d) (Fin d) ℂ)‖ = _
  rw [← sub_mul, CStarRing.norm_mul_mem_unitary _
    (Matrix.specialUnitaryGroup_le_unitaryGroup W.property)]
  rfl

lemma residual_distance (U V : SU d) : opDist 1 (U * V⁻¹) = opDist U V := by
  rw [opDist_symm]
  simpa using opDist_mul_right U V V⁻¹

lemma seqUnitary_invSeq (S : List (SU d)) : seqUnitary (invSeq S) = (seqUnitary S)⁻¹ :=
  (List.prod_inv_reverse S).symm

lemma invSeq_mem {G : Finset (SU d)} (hG : ∀ g ∈ G, g⁻¹ ∈ G)
    {S : List (SU d)} (hS : ∀ g ∈ S, g ∈ G) : ∀ g ∈ invSeq S, g ∈ G := by
  intro g hg
  simp only [invSeq, List.mem_reverse, List.mem_map] at hg
  obtain ⟨a, ha, rfl⟩ := hg
  exact hG a (hS a ha)

lemma epsSeq_zero (c e : ℝ) : epsSeq c e 0 = e := rfl

lemma epsSeq_succ (c e : ℝ) (n : ℕ) :
    epsSeq c e (n + 1) = c * epsSeq c e n ^ ((3 : ℝ) / 2) := by
  exact Function.iterate_succ_apply' _ _ _

lemma three_halves (x : ℝ) (hx : 0 < x) :
    x ^ ((3 : ℝ) / 2) = x * Real.sqrt x := by
  calc
    x ^ ((3 : ℝ) / 2) = x ^ (1 + 1 / (2 : ℝ)) := by norm_num
    _ = x * Real.sqrt x := by rw [Real.rpow_add hx, Real.rpow_one, ← Real.sqrt_eq_rpow]

lemma step_le (c x : ℝ) (hc : 0 < c) (hx : 0 < x) (hsmall : x ≤ 1 / c ^ 2) :
    c * x ^ ((3 : ℝ) / 2) ≤ x := by
  have hs : c * Real.sqrt x ≤ 1 := by
    have hsq := Real.sq_sqrt hx.le
    have hb : x * c ^ 2 ≤ 1 := (le_div_iff₀ (sq_pos_of_pos hc)).mp hsmall
    nlinarith [Real.sqrt_nonneg x, sq_nonneg (c * Real.sqrt x - 1)]
  rw [three_halves x hx]
  nlinarith

lemma epsSeq_pos_le (c e : ℝ) (hc : 0 < c) (he : 0 < e)
    (hsmall : e ≤ 1 / c ^ 2) (n : ℕ) : 0 < epsSeq c e n ∧ epsSeq c e n ≤ e := by
  induction n with
  | zero => exact ⟨he, le_rfl⟩
  | succ n ih =>
    rw [epsSeq_succ]
    exact ⟨mul_pos hc (Real.rpow_pos_of_pos ih.1 _),
      (step_le c _ hc ih.1 (ih.2.trans hsmall)).trans ih.2⟩

lemma perturbation_bound (b e : ℝ) (_hb : 0 < b) (he : 0 < e) (he1 : e ≤ 1) :
    8 * e * (b * Real.sqrt e) + 4 * e * (b * Real.sqrt e) ^ 2 +
      8 * e ^ 2 + 4 * e ^ 3 + e ^ 4 ≤
        (8 * b + 4 * b ^ 2 + 13) * e ^ ((3 : ℝ) / 2) := by
  have h2 : e ^ 2 ≤ e ^ ((3 : ℝ) / 2) := by
    simpa using Real.rpow_le_rpow_of_exponent_ge he he1 (show (3 : ℝ) / 2 ≤ 2 by norm_num)
  have h3 : e ^ 3 ≤ e ^ ((3 : ℝ) / 2) := by
    simpa using Real.rpow_le_rpow_of_exponent_ge he he1 (show (3 : ℝ) / 2 ≤ 3 by norm_num)
  have h4 : e ^ 4 ≤ e ^ ((3 : ℝ) / 2) := by
    simpa using Real.rpow_le_rpow_of_exponent_ge he he1 (show (3 : ℝ) / 2 ≤ 4 by norm_num)
  have hs := Real.sq_sqrt he.le
  have hb2 := mul_le_mul_of_nonneg_left h2 (sq_nonneg b)
  have hterm : 4 * e * (b * Real.sqrt e) ^ 2 = 4 * b ^ 2 * e ^ 2 := by
    rw [mul_pow, hs]
    ring
  rw [hterm, three_halves e he]
  rw [three_halves e he] at h2 h3 h4 hb2
  nlinarith

end SKAlgorithm.Qudit.RecursionProof


open scoped Matrix Matrix.Norms.L2Operator
open QAlgorithms SKAlgorithm.Qudit SKAlgorithm.Qudit.RecursionProof

namespace SKAlgorithm.Qudit.RecursionProof

lemma commutator_perturbation {d : ℕ} (V W Vt Wt : SU d) (e δ : ℝ)
    (hVt : opDist V Vt < e) (hWt : opDist W Wt < e)
    (hV : opDist 1 V < δ) (hW : opDist 1 W < δ) :
    opDist (V * W * V⁻¹ * W⁻¹) (Vt * Wt * Vt⁻¹ * Wt⁻¹) <
      8 * e * δ + 4 * e * δ ^ 2 + 8 * e ^ 2 + 4 * e ^ 3 + e ^ 4 := by
  exact @lemma_1 d V W Vt Wt
    V.property.1
    W.property.1
    Vt.property.1
    Wt.property.1 e δ hVt hWt hV hW

end SKAlgorithm.Qudit.RecursionProof

theorem solution (d : ℕ) (c' c'' : ℝ) (hc' : 0 < c') (hc'' : 0 < c'') :
    ∃ c εs : ℝ, 0 < c ∧ 0 < εs ∧
      ∀ (G : Finset (SU d)), (∀ g ∈ G, g⁻¹ ∈ G) →
      ∀ (ε₀ : ℝ) (l₀ : ℕ), 0 < ε₀ → ε₀ ≤ εs →
      ∀ (basic : SU d → List (SU d)) (gc : ℕ → SU d → SU d × SU d),
        (∀ U : SU d, (∀ g ∈ basic U, g ∈ G) ∧ (basic U).length ≤ l₀ ∧
          opDist U (seqUnitary (basic U)) < ε₀) →
        (∀ (k : ℕ) (Δ : SU d), opDist 1 Δ < epsSeq c ε₀ k →
          opDist ((gc k Δ).1 * (gc k Δ).2 * (gc k Δ).1⁻¹ * (gc k Δ).2⁻¹) Δ <
              c' * epsSeq c ε₀ k ^ ((3 : ℝ) / 2) ∧
            opDist 1 (gc k Δ).1 < c'' * Real.sqrt (epsSeq c ε₀ k) ∧
            opDist 1 (gc k Δ).2 < c'' * Real.sqrt (epsSeq c ε₀ k)) →
        ∀ (n : ℕ) (U : SU d),
          (∀ g ∈ solovayKitaev basic gc n U, g ∈ G) ∧
          (solovayKitaev basic gc n U).length ≤ 5 ^ n * l₀ ∧
          opDist U (seqUnitary (solovayKitaev basic gc n U)) < epsSeq c ε₀ n := by
  classical
  let c : ℝ := c' + 8 * c'' + 4 * c'' ^ 2 + 13
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, min 1 (1 / c ^ 2), hc, lt_min (by norm_num) (by positivity), ?_⟩
  intro G hG e l he hes basic gc hbasic hgc
  have hsmall : e ≤ 1 / c ^ 2 := hes.trans (min_le_right _ _)
  have he1 : e ≤ 1 := hes.trans (min_le_left _ _)
  intro n
  induction n with
  | zero => intro U; simpa [solovayKitaev, epsSeq_zero] using hbasic U
  | succ n ih =>
    intro U
    let Un := solovayKitaev basic gc n U
    let Δ := U * (seqUnitary Un)⁻¹
    let V := (gc n Δ).1
    let W := (gc n Δ).2
    let Vn := solovayKitaev basic gc n V
    let Wn := solovayKitaev basic gc n W
    have hUn := ih U
    have hVn := ih V
    have hWn := ih W
    have hep := epsSeq_pos_le c e hc he hsmall n
    have hΔ : opDist 1 Δ < epsSeq c e n := by
      rw [residual_distance]
      exact hUn.2.2
    obtain ⟨hgcerr, hV, hW⟩ := hgc n Δ hΔ
    change opDist (V * W * V⁻¹ * W⁻¹) Δ < _ at hgcerr
    change opDist 1 V < _ at hV
    change opDist 1 W < _ at hW
    change (∀ g ∈ Vn ++ Wn ++ invSeq Vn ++ invSeq Wn ++ Un, g ∈ G) ∧
      (Vn ++ Wn ++ invSeq Vn ++ invSeq Wn ++ Un).length ≤ 5 ^ (n + 1) * l ∧ _
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      have hVi := invSeq_mem hG hVn.1
      have hWi := invSeq_mem hG hWn.1
      simp only [List.mem_append] at hg
      rcases hg with (((h | h) | h) | h) | h
      · exact hVn.1 g h
      · exact hWn.1 g h
      · exact hVi g h
      · exact hWi g h
      · exact hUn.1 g h
    · have hUlen : Un.length ≤ 5 ^ n * l := hUn.2.1
      have hVlen : Vn.length ≤ 5 ^ n * l := hVn.2.1
      have hWlen : Wn.length ≤ 5 ^ n * l := hWn.2.1
      simp only [List.length_append, invSeq, List.length_reverse, List.length_map]
      calc
        _ ≤ 5 * (5 ^ n * l) := by omega
        _ = 5 ^ (n + 1) * l := by ring
    · have hpert : opDist (V * W * V⁻¹ * W⁻¹)
          (seqUnitary Vn * seqUnitary Wn * (seqUnitary Vn)⁻¹ * (seqUnitary Wn)⁻¹) <
          8 * epsSeq c e n * (c'' * Real.sqrt (epsSeq c e n)) +
          4 * epsSeq c e n * (c'' * Real.sqrt (epsSeq c e n)) ^ 2 +
          8 * epsSeq c e n ^ 2 + 4 * epsSeq c e n ^ 3 + epsSeq c e n ^ 4 := by
        exact RecursionProof.commutator_perturbation V W (seqUnitary Vn) (seqUnitary Wn)
          (epsSeq c e n) (c'' * Real.sqrt (epsSeq c e n)) hVn.2.2 hWn.2.2 hV hW
      have hpert' := hpert.trans_le (perturbation_bound c'' _ hc'' hep.1 (hep.2.trans he1))
      have hfinal : opDist Δ
          (seqUnitary Vn * seqUnitary Wn * (seqUnitary Vn)⁻¹ * (seqUnitary Wn)⁻¹) <
          c * epsSeq c e n ^ ((3 : ℝ) / 2) := by
        calc
          _ ≤ opDist Δ (V * W * V⁻¹ * W⁻¹) +
              opDist (V * W * V⁻¹ * W⁻¹)
                (seqUnitary Vn * seqUnitary Wn * (seqUnitary Vn)⁻¹ * (seqUnitary Wn)⁻¹) :=
            opDist_triangle _ _ _
          _ < c' * epsSeq c e n ^ ((3 : ℝ) / 2) +
              (8 * c'' + 4 * c'' ^ 2 + 13) * epsSeq c e n ^ ((3 : ℝ) / 2) := by
            rw [opDist_symm Δ]
            exact add_lt_add hgcerr hpert'
          _ = _ := by dsimp [c]; ring
      rw [epsSeq_succ]
      have hproduct := opDist_mul_right Δ
        (seqUnitary Vn * seqUnitary Wn * (seqUnitary Vn)⁻¹ * (seqUnitary Wn)⁻¹)
        (seqUnitary Un)
      have hseq : seqUnitary (Vn ++ Wn ++ invSeq Vn ++ invSeq Wn ++ Un) =
          (seqUnitary Vn * seqUnitary Wn * (seqUnitary Vn)⁻¹ * (seqUnitary Wn)⁻¹) *
            seqUnitary Un := by
        simp only [seqUnitary, List.prod_append, invSeq, ← List.prod_inv_reverse]
      change opDist U (seqUnitary (Vn ++ Wn ++ invSeq Vn ++ invSeq Wn ++ Un)) < _
      rw [hseq]
      rw [← hproduct] at hfinal
      simpa only [Δ, mul_assoc, inv_mul_cancel, mul_one] using hfinal

