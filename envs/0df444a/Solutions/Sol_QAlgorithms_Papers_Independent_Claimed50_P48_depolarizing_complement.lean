-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P48.depolarizing_complement
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T11:03:30.293348+00:00
-- url     : https://prove2.me/submissions/d0eb0cb7-59a9-43cb-b071-9a28aa6f950c

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P48
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Claimed50 QAlgorithms.Papers.Independent.Claimed50.P48

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Information100.P67 (receiverChannel complementaryChannel environmentSwap)

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble convexRoof)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D A2 B2 C2 K : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype A2] [DecidableEq A2] [Fintype B2] [DecidableEq B2]

variable [Fintype C2] [DecidableEq C2] [Fintype K] [DecidableEq K]

/-- dilation built from an operator on `A × B`. -/
def g68qV (S : Matrix (C × C) (A × B) ℂ) : Matrix (B × C × C) A ℂ := fun bp i => S bp.2 (i, bp.1)

theorem g68q_comp (S : Matrix (C × C) (A × B) ℂ) (rho : Matrix A A ℂ) :
    complementaryChannel (g68qV S) rho = S * (rho ⊗ₖ (1 : Matrix B B ℂ)) * Sᴴ := by
  ext p p'
  simp only [complementaryChannel, traceLeft, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    g68qV, Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type, Finset.sum_mul, mul_ite, mul_one,
    mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_comm]

theorem g68q_recv (S : Matrix (C × C) (A × B) ℂ) (rho : Matrix A A ℂ) (b b' : B) :
    receiverChannel (g68qV S) rho b b' = ∑ i, ∑ i', rho i i' * (Sᴴ * S) (i', b') (i, b) := by
  simp only [receiverChannel, traceRight, Matrix.mul_apply, Matrix.conjTranspose_apply,
    g68qV, Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
  simp only [Matrix.of_apply]
  simp only [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv (Equiv.mk (fun x : C × C × A × A => ((x.2.2.2, x.2.2.1, x.1, x.2.1) : A × A × C × C))
    (fun y => (y.2.2.1, y.2.2.2, y.2.1, y.1)) (fun _ => rfl) (fun _ => rfl)) _ _ (fun x => ?_)
  simp only [Equiv.coe_fn_mk]; ring

theorem g68q_iso (S : Matrix (C × C) (A × B) ℂ) (i i' : A) :
    ((g68qV S)ᴴ * g68qV S) i i' = ∑ b, (Sᴴ * S) (i, b) (i', b) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, g68qV, Fintype.sum_prod_type]

theorem g68q_P_apply (d : ℕ) [Nonempty (Fin d)] (p q : Fin d × Fin d) :
    pureDensity (finiteMaxEntangled (Fin d)) p q = if p.1 = p.2 ∧ q.1 = q.2 then ((d : ℂ))⁻¹ else 0 := by
  have hs : ((Real.sqrt d : ℂ))⁻¹ * ((Real.sqrt d : ℂ))⁻¹ = ((d : ℂ))⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]; push_cast; ring
  by_cases h1 : p.1 = p.2 <;> by_cases h2 : q.1 = q.2 <;>
    simp [pureDensity, finiteMaxEntangled, h1, h2, hs]

theorem g68q_PP (d : ℕ) [Nonempty (Fin d)] (hd : 0 < d) :
    pureDensity (finiteMaxEntangled (Fin d)) * pureDensity (finiteMaxEntangled (Fin d)) =
      pureDensity (finiteMaxEntangled (Fin d)) := by
  ext p q
  simp only [Matrix.mul_apply, g68q_P_apply, Fintype.sum_prod_type]
  by_cases h1 : p.1 = p.2 <;> by_cases h2 : q.1 = q.2 <;> simp [h1, h2, ite_and]
  have : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp

theorem g68q_PH (d : ℕ) [Nonempty (Fin d)] :
    (pureDensity (finiteMaxEntangled (Fin d)))ᴴ = pureDensity (finiteMaxEntangled (Fin d)) := by
  ext p q
  simp only [Matrix.conjTranspose_apply, g68q_P_apply]
  by_cases h1 : p.1 = p.2 <;> by_cases h2 : q.1 = q.2 <;> simp [h1, h2]

theorem g68q_SS (d : ℕ) [Nonempty (Fin d)] (hd : 0 < d) (α κ : ℝ) :
    ((α : ℂ) • (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) + (κ : ℂ) • pureDensity (finiteMaxEntangled (Fin d)))ᴴ *
      ((α : ℂ) • 1 + (κ : ℂ) • pureDensity (finiteMaxEntangled (Fin d))) =
      ((α ^ 2 : ℝ) : ℂ) • 1 + ((2 * α * κ + κ ^ 2 : ℝ) : ℂ) • pureDensity (finiteMaxEntangled (Fin d)) := by
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul, g68q_PH,
    Matrix.conjTranspose_one]
  simp only [Complex.star_def, Complex.conj_ofReal, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, g68q_PP d hd, smul_smul]
  push_cast
  rw [show (2 * (α : ℂ) * κ + κ ^ 2) = α * κ + κ * α + κ * κ by ring, add_smul, add_smul]
  rw [show (α : ℂ) ^ 2 = α * α by ring]
  simp only [smul_add, smul_smul]
  abel

theorem g68q_recv2 (d : ℕ) [Nonempty (Fin d)] (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (a g : ℝ)
    (h : Sᴴ * S = (a : ℂ) • 1 + (g : ℂ) • pureDensity (finiteMaxEntangled (Fin d)))
    (rho : Matrix (Fin d) (Fin d) ℂ) :
    receiverChannel (g68qV S) rho = ((a : ℂ) * rho.trace) • 1 + ((g : ℂ) / d) • rho := by
  ext b b'
  rw [g68q_recv, h]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, g68q_P_apply, smul_eq_mul, Prod.mk.injEq,
    mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, ite_and]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq', Matrix.trace, Finset.mul_sum, eq_comm]
  split_ifs
  · rw [Finset.sum_congr rfl (fun x _ => mul_comm (rho x x) (a : ℂ))]; ring
  · ring

theorem g68q_iso2 (d : ℕ) [Nonempty (Fin d)] (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (a g : ℝ)
    (h : Sᴴ * S = (a : ℂ) • 1 + (g : ℂ) • pureDensity (finiteMaxEntangled (Fin d))) :
    (g68qV S)ᴴ * g68qV S = ((a : ℂ) * d + (g : ℂ) / d) • 1 := by
  ext i i'
  rw [g68q_iso, h]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, g68q_P_apply, smul_eq_mul, Prod.mk.injEq,
    mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, ite_and]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq', eq_comm]
  split_ifs
  · ring
  · ring

theorem g68q_kc1 (E : K → Matrix B A ℂ) :
    receiverChannel (indexedKrausDilation E) = krausApply E := by
  funext rho; ext b b'
  simp only [receiverChannel, traceRight, krausApply, Matrix.of_apply, Matrix.sum_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, indexedKrausDilation, Fintype.sum_prod_type]

theorem g68q_kc2 (E : K → Matrix B A ℂ) (rho : Matrix A A ℂ) (a b : K) :
    complementaryChannel (indexedKrausDilation E) rho a b = (E a * rho * (E b)ᴴ).trace := by
  simp only [complementaryChannel, traceLeft, Matrix.trace, Matrix.diag, Matrix.of_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, indexedKrausDilation, Fintype.sum_prod_type]

theorem g68q_kc3 (E : K → Matrix B A ℂ) :
    complementaryChannel (indexedKrausDilation E) = krausApply (rowKraus E) := by
  funext rho; ext a b
  rw [g68q_kc2]
  simp only [krausApply, Matrix.trace, Matrix.diag, Matrix.sum_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, rowKraus]

theorem g68q_isChannel_of {ι κ K' : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [Fintype K']
    (E : K' → Matrix κ ι ℂ) (hE : ∑ k, (E k)ᴴ * E k = 1) (Φ : Superop ι κ) (h : Φ = krausApply E) :
    IsChannel Φ := by
  refine ⟨Fintype.card K', fun i => E ((Fintype.equivFin K').symm i), ?_, fun rho => ?_⟩
  · unfold IsKrausFamily
    rw [← hE]
    exact Equiv.sum_comp (Fintype.equivFin K').symm (fun k => (E k)ᴴ * E k)
  · rw [h]
    exact (Equiv.sum_comp (Fintype.equivFin K').symm (fun k => E k * rho * (E k)ᴴ)).symm

theorem g68q_chan (V : Matrix (B × K) A ℂ) (hV : Vᴴ * V = 1) :
    IsChannel (receiverChannel V) ∧ IsChannel (complementaryChannel V) := by
  let E : K → Matrix B A ℂ := fun k b a => V (b, k) a
  have hVE : indexedKrausDilation E = V := by ext p a; rfl
  have h1 : ∑ k, (E k)ᴴ * E k = 1 := by
    rw [← hV]; ext a a'
    simp only [E, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type]
    exact Finset.sum_comm
  have h2 : ∑ b, (rowKraus E b)ᴴ * rowKraus E b = 1 := by
    rw [← h1]; ext a a'
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, rowKraus]
    exact Finset.sum_comm
  refine ⟨g68q_isChannel_of E h1 _ ?_, g68q_isChannel_of (rowKraus E) h2 _ ?_⟩
  · rw [← hVE, g68q_kc1]
  · rw [← hVE, g68q_kc3]

theorem g68q_const (d : ℕ) (hd : 2 ≤ d) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ (d : ℝ)^2 / ((d : ℝ)^2 - 1)) :
    Real.sqrt (t / d) ^ 2 = t / d ∧
    2 * Real.sqrt (t / d) * (Real.sqrt d * (-(Real.sqrt t) / d + Real.sqrt (1 - t * ((d : ℝ)^2 - 1) / (d : ℝ)^2))) +
      (Real.sqrt d * (-(Real.sqrt t) / d + Real.sqrt (1 - t * ((d : ℝ)^2 - 1) / (d : ℝ)^2))) ^ 2 = d * (1 - t) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdp : (0 : ℝ) < d := by linarith
  have hq : 0 < (d : ℝ) ^ 2 - 1 := by nlinarith
  have hw0 : 0 ≤ 1 - t * ((d : ℝ)^2 - 1) / (d : ℝ)^2 := by
    rw [le_div_iff₀ hq] at ht1
    rw [sub_nonneg, div_le_one (by positivity)]; linarith
  refine ⟨Real.sq_sqrt (div_nonneg ht0 hdp.le), ?_⟩
  rw [Real.sqrt_div' t hdp.le]
  have es := Real.sq_sqrt ht0
  have er := Real.sq_sqrt hdp.le
  have ew := Real.sq_sqrt hw0
  have hr : 0 < Real.sqrt d := Real.sqrt_pos.mpr hdp
  generalize Real.sqrt (1 - t * ((d : ℝ)^2 - 1) / (d : ℝ)^2) = w at *
  generalize Real.sqrt t = s at *
  generalize Real.sqrt d = r at *
  field_simp
  rw [← er] at ew ⊢
  rw [← es] at ew ⊢
  field_simp at ew
  linear_combination r ^ 2 * ew

theorem g68q_WP (d : ℕ) [Nonempty (Fin d)] (U : Matrix (Fin d) (Fin d) ℂ) (hU : U * Uᴴ = 1) (hU' : Uᴴ * U = 1) :
    (U ⊗ₖ U.map conj) * pureDensity (finiteMaxEntangled (Fin d)) =
      pureDensity (finiteMaxEntangled (Fin d)) * (U ⊗ₖ U.map conj) := by
  ext p q
  simp only [Matrix.mul_apply, g68q_P_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.map_apply,
    mul_ite, mul_zero, ite_mul, zero_mul, ite_and]
  have e1 := congrFun (congrFun hU p.1) p.2
  have e2 := congrFun (congrFun hU' q.2) q.1
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, RCLike.star_def] at e1 e2
  have e2' : ∑ j, U j q.1 * (starRingEnd ℂ) (U j q.2) = if q.1 = q.2 then 1 else 0 := by
    rw [Finset.sum_congr rfl (fun j _ => mul_comm (U j q.1) _), e2]
    by_cases h : q.1 = q.2 <;> simp [h, Ne.symm]
  by_cases h1 : p.1 = p.2 <;> by_cases h2 : q.1 = q.2 <;> simp [h1, h2, Finset.sum_ite_eq', Finset.sum_ite_eq]
  · rw [← Finset.sum_mul, ← Finset.mul_sum]
    rw [h1] at e1; rw [h2] at e2'; simp at e1 e2'; rw [e1, e2']; ring
  · rw [← Finset.mul_sum, e2']; simp [h2]
  · rw [← Finset.sum_mul, e1]; simp [h1]

theorem solution (d : ℕ) (hd : 2 ≤ d) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ (d : ℝ)^2 / ((d : ℝ)^2 - 1)) :
    let hpos : 0 < d := lt_of_lt_of_le (by decide : 0 < 2) hd
    IsChannel (QuditFidelity.depolarizingMap d hpos t) ∧ IsChannel (depolarizingComplement d hpos t) ∧
    CPComplementary (QuditFidelity.depolarizingMap d hpos t) (depolarizingComplement d hpos t) ∧
    (∀ (U : Matrix.unitaryGroup (Fin d) ℂ) rho,
      depolarizingComplement d hpos t ((U : Matrix (Fin d) (Fin d) ℂ) * rho * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) =
      ((U : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ (U : Matrix (Fin d) (Fin d) ℂ).map conj) *
        depolarizingComplement d hpos t rho *
        ((U : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ (U : Matrix (Fin d) (Fin d) ℂ).map conj)ᴴ) ∧
    (∀ (U : Matrix.unitaryGroup (Fin d) ℂ) rho,
      QuditFidelity.depolarizingMap d hpos t
          ((U : Matrix (Fin d) (Fin d) ℂ) * rho * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) =
        (U : Matrix (Fin d) (Fin d) ℂ) * QuditFidelity.depolarizingMap d hpos t rho *
          (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) := by
  intro hpos
  haveI : Nonempty (Fin d) := ⟨⟨0, hpos⟩⟩
  set α : ℝ := Real.sqrt (t / d) with hα
  set κ : ℝ := Real.sqrt d * (-(Real.sqrt t) / d + Real.sqrt (1 - t * ((d : ℝ)^2 - 1) / (d : ℝ)^2)) with hκ
  set P := pureDensity (finiteMaxEntangled (Fin d)) with hP
  set S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ := (α : ℂ) • 1 + (κ : ℂ) • P with hS
  have hSdef : depolarizingS d hpos t = S := by
    simp only [depolarizingS, hS, hα, hκ, hP]
    push_cast
    rfl
  obtain ⟨c1, c2⟩ := g68q_const d hd t ht0 ht1
  have hSS : Sᴴ * S = ((t / d : ℝ) : ℂ) • 1 + ((d * (1 - t) : ℝ) : ℂ) • P := by
    rw [hS, g68q_SS d hpos α κ, c1, ← c2]
  have hSH : Sᴴ = S := by
    rw [hS, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul, hP, g68q_PH,
      Matrix.conjTranspose_one]
    simp [Complex.conj_ofReal]
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hrecv : receiverChannel (g68qV S) = QuditFidelity.depolarizingMap d hpos t := by
    funext rho
    rw [g68q_recv2 d S _ _ hSS rho]
    simp only [QuditFidelity.depolarizingMap]
    push_cast
    congr 1
    all_goals (try congr 1)
    all_goals (try field_simp)
    all_goals (try ring)
  have hcomp : complementaryChannel (g68qV S) = depolarizingComplement d hpos t := by
    funext rho
    rw [g68q_comp, hSH, depolarizingComplement, hSdef]
  have hiso : (g68qV S)ᴴ * g68qV S = 1 := by
    rw [g68q_iso2 d S _ _ hSS]
    push_cast
    rw [show ((t : ℂ) / d * d + d * (1 - t) / d) = 1 by field_simp; ring, one_smul]
  obtain ⟨ch1, ch2⟩ := g68q_chan (g68qV S) hiso
  rw [hrecv] at ch1
  rw [hcomp] at ch2
  refine ⟨ch1, ch2, ⟨g68qV S, hrecv, hcomp⟩, ?_, ?_⟩
  · intro U rho
    set V : Matrix (Fin d) (Fin d) ℂ := (U : Matrix (Fin d) (Fin d) ℂ)
    have hU : V * Vᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp U.2
    have hU' : Vᴴ * V = 1 := Matrix.mem_unitaryGroup_iff'.mp U.2
    have hc : V.map conj * (V.map conj)ᴴ = 1 := by
      have : (V.map conj)ᴴ = (Vᴴ).map conj := by ext i j; simp [Matrix.conjTranspose_apply]
      rw [this, ← Matrix.map_mul, hU]; ext i j; simp [Matrix.one_apply]
    set W := V ⊗ₖ V.map conj
    have hk : (V * rho * Vᴴ) ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ) = W * (rho ⊗ₖ 1) * Wᴴ := by
      rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
        Matrix.mul_one, hc]
    have hWS : W * S = S * W := by
      rw [hS, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_one, Matrix.one_mul, hP, g68q_WP d V hU hU']
    have hWS' : Wᴴ * S = S * Wᴴ := by
      have := congrArg Matrix.conjTranspose hWS
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hSH] at this
      exact this.symm
    simp only [depolarizingComplement, hSdef, hk]
    simp only [← Matrix.mul_assoc, hWS]
    simp only [Matrix.mul_assoc, hWS']
  · intro U rho
    set V : Matrix (Fin d) (Fin d) ℂ := (U : Matrix (Fin d) (Fin d) ℂ)
    have hU : V * Vᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp U.2
    have hU' : Vᴴ * V = 1 := Matrix.mem_unitaryGroup_iff'.mp U.2
    have htr : (V * rho * Vᴴ).trace = rho.trace := by
      rw [Matrix.trace_mul_cycle, hU', Matrix.one_mul]
    simp only [QuditFidelity.depolarizingMap]
    rw [htr]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, hU, Matrix.mul_assoc]
