-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P07.lemma2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T05:54:47.47313+00:00
-- url     : https://prove2.me/submissions/44c100da-8c6b-4311-92df-93340e744205

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P07

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Information100.P04 (Measurement)

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P07

lemma h54c_cfc_trace {n : Type} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma h54c_vn_nonneg {n : Type} [Fintype n] [DecidableEq n] (ρ : Matrix n n ℂ)
    (h : ρ.PosSemidef) (ht : ρ.trace = 1) : 0 ≤ vnEntropy ρ := by
  have hH := h.isHermitian
  unfold vnEntropy
  rw [h54c_cfc_trace hH]
  have hsum : ∑ i, hH.eigenvalues i = 1 := by
    have := hH.trace_eq_sum_eigenvalues
    rw [ht] at this
    have h2 := congrArg Complex.re this
    simp at h2
    exact h2.symm
  have hnn : ∀ i, 0 ≤ hH.eigenvalues i := fun i => h.eigenvalues_nonneg i
  have hle : ∀ i, hH.eigenvalues i ≤ 1 := by
    intro i
    rw [← hsum]
    exact Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)
  rw [Complex.re_sum]
  simp only [Complex.ofReal_re]
  rw [neg_nonneg]
  apply Finset.sum_nonpos
  intro i _
  exact mul_nonpos_of_nonneg_of_nonpos (hnn i) (Real.logb_nonpos (by norm_num) (hnn i) (hle i))

lemma h54c_auxProb_nonneg {X Q : Type} [Fintype X] [Fintype Q] (E : CQData X Q) (hE : E.Valid)
    (V : Auxiliary X) (u : Fin V.size) : 0 ≤ auxProb E V u :=
  Finset.sum_nonneg (fun x _ => mul_nonneg (hE.1 x) (V.nonnegative x u))

lemma h54c_auxState_vn {X Q : Type} [Fintype X] [Fintype Q] [DecidableEq Q]
    (E : CQData X Q) (hE : E.Valid) (V : Auxiliary X) (u : Fin V.size) :
    0 ≤ auxProb E V u * vnEntropy (auxState E V u) := by
  have hp := h54c_auxProb_nonneg E hE V u
  rcases hp.eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  apply mul_nonneg hp
  apply h54c_vn_nonneg
  · unfold auxState
    apply Matrix.PosSemidef.smul _ (by
      have : (0:ℝ) ≤ (auxProb E V u)⁻¹ := inv_nonneg.mpr hp
      exact_mod_cast (Complex.zero_le_real.mpr this))
    apply Matrix.posSemidef_sum
    intro x _
    apply Matrix.PosSemidef.smul (hE.2.2 x).1
    exact Complex.zero_le_real.mpr (mul_nonneg (hE.1 x) (V.nonnegative x u))
  · unfold auxState
    rw [Matrix.trace_smul, Matrix.trace_sum]
    simp only [Matrix.trace_smul, (hE.2.2 _).2, smul_eq_mul, mul_one]
    rw [← Complex.ofReal_sum]
    have : ∑ x, auxJoint E V (u, x) = auxProb E V u := rfl
    rw [this]
    have hne : (auxProb E V u : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    field_simp

lemma h54c_auxIQ_le {X Q : Type} [Fintype X] [Fintype Q] [DecidableEq Q]
    (E : CQData X Q) (hE : E.Valid) (V : Auxiliary X) :
    auxIQ E V ≤ vnEntropy (ensembleMean E) := by
  unfold auxIQ quantumGivenAux
  have := Finset.sum_nonneg (fun u (_ : u ∈ Finset.univ) => h54c_auxState_vn E hE V u)
  linarith

lemma h54c_const {X Q : Type} [Fintype X] [Fintype Q] [DecidableEq Q]
    (E : CQData X Q) (hE : E.Valid) :
    auxIQ E (constantAux X) = 0 ∧ auxCost E (constantAux X) = 0 := by
  have hp : ∀ u, auxProb E (constantAux X) u = 1 := by
    intro u; unfold auxProb auxJoint; simp [constantAux, hE.2.1]
  have hS : ∀ u, auxState E (constantAux X) u = ensembleMean E := by
    intro u; unfold auxState; rw [hp]
    simp [auxJoint, constantAux, ensembleMean, QAlgorithms.Papers.Independent.Information100.P27.average]
  have hQ : quantumGivenAux E (constantAux X) = vnEntropy (ensembleMean E) := by
    unfold quantumGivenAux
    simp only [hp, hS, one_mul]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp [constantAux]
  have hIQ : auxIQ E (constantAux X) = 0 := by unfold auxIQ; rw [hQ]; ring
  refine ⟨hIQ, ?_⟩
  unfold auxCost auxIX
  rw [hIQ]
  have h1 : shannon (auxProb E (constantAux X)) = 0 := by
    unfold shannon; simp [hp]
  have h2 : shannon (auxJoint E (constantAux X)) = shannon E.prob := by
    unfold shannon
    rw [Fintype.sum_prod_type]
    change -∑ u : Fin 1, _ = _
    rw [Fin.sum_univ_one]
    simp [auxJoint, constantAux]
  rw [h1, h2]; ring

def h54c_mix {X : Type} (V1 V2 : Auxiliary X) (l : ℝ) (h0 : 0 ≤ l) (h1 : l ≤ 1) : Auxiliary X where
  size := V1.size + V2.size
  positive := by have := V1.positive; omega
  channel := fun x => Fin.addCases (motive := fun _ => ℝ)
    (fun u => l * V1.channel x u) (fun u => (1-l) * V2.channel x u)
  nonnegative := by
    intro x u
    refine Fin.addCases (fun u => ?_) (fun u => ?_) u
    · simp only [Fin.addCases_left]; exact mul_nonneg h0 (V1.nonnegative x u)
    · simp only [Fin.addCases_right]; exact mul_nonneg (by linarith) (V2.nonnegative x u)
  normalized := by
    intro x
    rw [Fin.sum_univ_add]
    simp only [Fin.addCases_left, Fin.addCases_right, ← Finset.mul_sum, V1.normalized, V2.normalized]
    ring

lemma h54c_mlog (c q : ℝ) : (c*q) * Real.logb 2 (c*q) = c*q*Real.logb 2 c + c*(q*Real.logb 2 q) := by
  rcases eq_or_ne c 0 with hc | hc
  · simp [hc]
  rcases eq_or_ne q 0 with hq | hq
  · simp [hq]
  rw [Real.logb_mul hc hq]; ring

lemma h54c_scale {Y : Type} [Fintype Y] (c : ℝ) (f : Y → ℝ) :
    ∑ y, (c * f y) * Real.logb 2 (c * f y) =
      c * Real.logb 2 c * ∑ y, f y + c * ∑ y, f y * Real.logb 2 (f y) := by
  simp only [h54c_mlog, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl; intro y _; ring

section mixsec
variable {X Q : Type} [Fintype X] [Fintype Q] [DecidableEq Q]
  (E : CQData X Q) (V1 V2 : Auxiliary X) (l : ℝ) (h0 : 0 ≤ l) (h1 : l ≤ 1)

lemma h54c_joint_l (u : Fin V1.size) (x : X) :
    auxJoint E (h54c_mix V1 V2 l h0 h1) (Fin.castAdd V2.size u, x) = l * auxJoint E V1 (u, x) := by
  simp only [auxJoint, h54c_mix, Fin.addCases_left]; ring

lemma h54c_joint_r (u : Fin V2.size) (x : X) :
    auxJoint E (h54c_mix V1 V2 l h0 h1) (Fin.natAdd V1.size u, x) = (1-l) * auxJoint E V2 (u, x) := by
  simp only [auxJoint, h54c_mix, Fin.addCases_right]; ring

lemma h54c_prob_l (u : Fin V1.size) :
    auxProb E (h54c_mix V1 V2 l h0 h1) (Fin.castAdd V2.size u) = l * auxProb E V1 u := by
  simp only [auxProb, h54c_joint_l, Finset.mul_sum]

lemma h54c_prob_r (u : Fin V2.size) :
    auxProb E (h54c_mix V1 V2 l h0 h1) (Fin.natAdd V1.size u) = (1-l) * auxProb E V2 u := by
  simp only [auxProb, h54c_joint_r, Finset.mul_sum]

lemma h54c_state_l (u : Fin V1.size) (hl : l ≠ 0) :
    auxState E (h54c_mix V1 V2 l h0 h1) (Fin.castAdd V2.size u) = auxState E V1 u := by
  unfold auxState
  rw [h54c_prob_l]
  simp only [h54c_joint_l]
  have hs : ∑ x, (((l * auxJoint E V1 (u,x) : ℝ)) : ℂ) • E.state x =
      ((l:ℝ):ℂ) • ∑ x, ((auxJoint E V1 (u,x) : ℝ):ℂ) • E.state x := by
    rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro x _
    rw [Complex.ofReal_mul, mul_smul]
  rw [hs, smul_smul]
  congr 1
  have : ((l:ℝ):ℂ) ≠ 0 := by exact_mod_cast hl
  rw [Complex.ofReal_mul, mul_inv]
  field_simp

lemma h54c_state_r (u : Fin V2.size) (hl : 1 - l ≠ 0) :
    auxState E (h54c_mix V1 V2 l h0 h1) (Fin.natAdd V1.size u) = auxState E V2 u := by
  unfold auxState
  rw [h54c_prob_r]
  simp only [h54c_joint_r]
  have hs : ∑ x, ((((1-l) * auxJoint E V2 (u,x) : ℝ)) : ℂ) • E.state x =
      (((1-l):ℝ):ℂ) • ∑ x, ((auxJoint E V2 (u,x) : ℝ):ℂ) • E.state x := by
    rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro x _
    rw [Complex.ofReal_mul, mul_smul]
  rw [hs, smul_smul]
  congr 1
  have : (((1-l):ℝ):ℂ) ≠ 0 := by exact_mod_cast hl
  rw [Complex.ofReal_mul, mul_inv]
  field_simp

lemma h54c_QA :
    quantumGivenAux E (h54c_mix V1 V2 l h0 h1) =
      l * quantumGivenAux E V1 + (1-l) * quantumGivenAux E V2 := by
  unfold quantumGivenAux
  change ∑ u : Fin (V1.size + V2.size), _ = _
  rw [Fin.sum_univ_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl; intro u _
    rw [h54c_prob_l]
    rcases eq_or_ne l 0 with hl | hl
    · simp [hl]
    · rw [h54c_state_l E V1 V2 l h0 h1 u hl]; ring
  · apply Finset.sum_congr rfl; intro u _
    rw [h54c_prob_r]
    rcases eq_or_ne (1-l) 0 with hl | hl
    · simp [hl]
    · rw [h54c_state_r E V1 V2 l h0 h1 u hl]; ring

lemma h54c_IQ :
    auxIQ E (h54c_mix V1 V2 l h0 h1) = l * auxIQ E V1 + (1-l) * auxIQ E V2 := by
  unfold auxIQ; rw [h54c_QA]; ring

lemma h54c_HU :
    shannon (auxProb E (h54c_mix V1 V2 l h0 h1)) =
      l * shannon (auxProb E V1) + (1-l) * shannon (auxProb E V2) -
      (l * Real.logb 2 l * ∑ u, auxProb E V1 u + (1-l) * Real.logb 2 (1-l) * ∑ u, auxProb E V2 u) := by
  unfold shannon
  change -∑ u : Fin (V1.size + V2.size), _ = _
  rw [Fin.sum_univ_add]
  simp only [h54c_prob_l, h54c_prob_r, h54c_scale]
  ring

lemma h54c_sumJ (g : ℝ → ℝ) : ∑ z, g (auxJoint E (h54c_mix V1 V2 l h0 h1) z) =
    ∑ z, g (l * auxJoint E V1 z) + ∑ z, g ((1-l) * auxJoint E V2 z) := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.sum_prod_type]
  change ∑ u : Fin (V1.size + V2.size), _ = _
  rw [Fin.sum_univ_add]
  simp only [h54c_joint_l, h54c_joint_r]

lemma h54c_HUX :
    shannon (auxJoint E (h54c_mix V1 V2 l h0 h1)) =
      l * shannon (auxJoint E V1) + (1-l) * shannon (auxJoint E V2) -
      (l * Real.logb 2 l * ∑ u, auxProb E V1 u + (1-l) * Real.logb 2 (1-l) * ∑ u, auxProb E V2 u) := by
  unfold shannon
  have h := h54c_sumJ E V1 V2 l h0 h1 (fun t => t * Real.logb 2 t)
  rw [h, h54c_scale, h54c_scale]
  have e1 : ∑ z, auxJoint E V1 z = ∑ u, auxProb E V1 u := by unfold auxProb; rw [Fintype.sum_prod_type]
  have e2 : ∑ z, auxJoint E V2 z = ∑ u, auxProb E V2 u := by unfold auxProb; rw [Fintype.sum_prod_type]
  rw [e1, e2]
  ring

lemma h54c_IX :
    auxIX E (h54c_mix V1 V2 l h0 h1) = l * auxIX E V1 + (1-l) * auxIX E V2 := by
  unfold auxIX; rw [h54c_HU, h54c_HUX]; ring

lemma h54c_cost :
    auxCost E (h54c_mix V1 V2 l h0 h1) = l * auxCost E V1 + (1-l) * auxCost E V2 := by
  unfold auxCost; rw [h54c_IX, h54c_IQ]; ring

end mixsec

lemma h54c_ne {X Q : Type} [Fintype X] [Fintype Q] [DecidableEq Q]
    (E : CQData X Q) (hE : E.Valid) (R : ℝ) (hR : 0 ≤ R) :
    ({v | ∃ V : Auxiliary X, auxCost E V ≤ R ∧ v = auxIQ E V} : Set ℝ).Nonempty :=
  ⟨0, constantAux X, by rw [(h54c_const E hE).2]; exact hR, (h54c_const E hE).1.symm⟩

lemma h54c_bdd {X Q : Type} [Fintype X] [Fintype Q] [DecidableEq Q]
    (E : CQData X Q) (hE : E.Valid) (R : ℝ) :
    BddAbove ({v | ∃ V : Auxiliary X, auxCost E V ≤ R ∧ v = auxIQ E V} : Set ℝ) := by
  refine ⟨vnEntropy (ensembleMean E), ?_⟩
  rintro v ⟨V, -, rfl⟩
  exact h54c_auxIQ_le E hE V

lemma h54c_mono {X Q : Type} [Fintype X] [Fintype Q] [DecidableEq Q]
    (E : CQData X Q) (hE : E.Valid) : MonotoneOn (dStar E) (Set.Ici 0) := by
  intro R1 h1 R2 _ h12
  unfold dStar
  apply csSup_le_csSup (h54c_bdd E hE R2) (h54c_ne E hE R1 h1)
  rintro v ⟨V, hV, rfl⟩
  exact ⟨V, hV.trans h12, rfl⟩

lemma h54c_conc {X Q : Type} [Fintype X] [Fintype Q] [DecidableEq Q]
    (E : CQData X Q) (hE : E.Valid) (R1 R2 l : ℝ) (h1 : 0 ≤ R1) (h2 : 0 ≤ R2)
    (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    l * dStar E R1 + (1-l) * dStar E R2 ≤ dStar E (l*R1+(1-l)*R2) := by
  apply le_of_forall_pos_le_add
  intro ε hε
  unfold dStar
  obtain ⟨v1, ⟨V1, hc1, rfl⟩, hv1⟩ := exists_lt_of_lt_csSup (h54c_ne E hE R1 h1)
    (show sSup {v | ∃ V : Auxiliary X, auxCost E V ≤ R1 ∧ v = auxIQ E V} - ε <
      sSup {v | ∃ V : Auxiliary X, auxCost E V ≤ R1 ∧ v = auxIQ E V} by linarith)
  obtain ⟨v2, ⟨V2, hc2, rfl⟩, hv2⟩ := exists_lt_of_lt_csSup (h54c_ne E hE R2 h2)
    (show sSup {v | ∃ V : Auxiliary X, auxCost E V ≤ R2 ∧ v = auxIQ E V} - ε <
      sSup {v | ∃ V : Auxiliary X, auxCost E V ≤ R2 ∧ v = auxIQ E V} by linarith)
  have hmem : auxIQ E (h54c_mix V1 V2 l hl0 hl1) ∈
      {v | ∃ V : Auxiliary X, auxCost E V ≤ l*R1+(1-l)*R2 ∧ v = auxIQ E V} := by
    refine ⟨h54c_mix V1 V2 l hl0 hl1, ?_, rfl⟩
    rw [h54c_cost]
    have : 0 ≤ 1 - l := by linarith
    nlinarith
  have hle := le_csSup (h54c_bdd E hE _) hmem
  rw [h54c_IQ] at hle
  have : 0 ≤ 1 - l := by linarith
  nlinarith

end QAlgorithms.Papers.Independent.Dependency50.P07

open QAlgorithms.Papers.Independent.Dependency50.P07

section CQStatements

variable {X Q Y T : Type} [Fintype X] [Fintype Q] [Fintype Y] [Fintype T]
  [DecidableEq X] [DecidableEq Q] [DecidableEq Y] [DecidableEq T]
  [Nonempty X] [Nonempty Q] [Nonempty Y] [Nonempty T]

/-- PDF pp.6--7, Lemma 2: both curves are nondecreasing and concave on the nonnegative half-line. -/
theorem solution (E : CQData X Q) (hE : E.Valid) :
    MonotoneOn (dStar E) (Set.Ici 0) ∧ MonotoneOn (cStar E) (Set.Ici 0) ∧
    (∀ R1 R2 l : ℝ, 0 ≤ R1 → 0 ≤ R2 → 0 ≤ l → l ≤ 1 →
      l * dStar E R1 + (1-l) * dStar E R2 ≤ dStar E (l*R1+(1-l)*R2)) ∧
    (∀ R1 R2 l : ℝ, 0 ≤ R1 → 0 ≤ R2 → 0 ≤ l → l ≤ 1 →
      l * cStar E R1 + (1-l) * cStar E R2 ≤ cStar E (l*R1+(1-l)*R2)) := by
  refine ⟨h54c_mono E hE, ?_, fun R1 R2 l h1 h2 h3 h4 => h54c_conc E hE R1 R2 l h1 h2 h3 h4, ?_⟩
  · intro R1 h1 R2 h2 h12
    unfold cStar
    have := h54c_mono E hE h1 h2 h12
    linarith
  · intro R1 R2 l h1 h2 h3 h4
    unfold cStar
    have := h54c_conc E hE R1 R2 l h1 h2 h3 h4
    linarith

end CQStatements

end
