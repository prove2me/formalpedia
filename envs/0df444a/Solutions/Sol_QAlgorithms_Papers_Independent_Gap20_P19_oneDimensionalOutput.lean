-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P19.oneDimensionalOutput
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T08:05:00.712216+00:00
-- url     : https://prove2.me/submissions/5d183180-0d21-448d-bc50-959ee9688d30

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P19
noncomputable section

open QAlgorithms
open QAlgorithms.Papers.Independent.Gap20.P19

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Kronecker

open Filter Topology

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel IsDegradable IsAntidegradable
   maximumCoherentInformation dilationPower)

open QAlgorithms.Papers.Independent.Claimed50.P48
  (MinimalDilation indexedKrausDilation arbitraryVectorComplement superopTensor tensorDilation)

open QAlgorithms.Papers.Independent.Claimed50.P24 (ChannelEB)

open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)

open QAlgorithms.Papers.Independent.Gap48.P36 (finWeyl WeylLabel)

open QAlgorithms.Papers.Independent.Information100.P69 (choi)

open QAlgorithms.Papers.Independent.Information100.P50 (matrixRange)

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C E F R K A2 B2 E2 : Type}

variable [Fintype A] [DecidableEq A] [Nonempty A]

variable [Fintype B] [DecidableEq B] [Nonempty B]

variable [Fintype C] [DecidableEq C] [Nonempty C]

variable [Fintype E] [DecidableEq E] [Nonempty E]

variable [Fintype F] [DecidableEq F] [Nonempty F]

variable [Fintype R] [DecidableEq R] [Nonempty R]

variable [Fintype K] [DecidableEq K]

variable [Fintype A2] [DecidableEq A2] [Nonempty A2]

variable [Fintype B2] [DecidableEq B2] [Nonempty B2]

variable [Fintype E2] [DecidableEq E2] [Nonempty E2]



lemma g79g_isChannel_of_kraus {K ι κ : Type} [Fintype K] [Fintype ι] [Fintype κ] [DecidableEq ι]
    (E : K → Matrix κ ι ℂ) (hE : IsKrausFamily E) : IsChannel (krausApply E) := by
  refine ⟨Fintype.card K, fun j => E ((Fintype.equivFin K).symm j), ?_, ?_⟩
  · unfold IsKrausFamily at *
    rw [← hE]; exact Equiv.sum_comp (Fintype.equivFin K).symm (fun k => (E k)ᴴ * E k)
  · intro r; unfold krausApply
    exact (Equiv.sum_comp (Fintype.equivFin K).symm (fun k => E k * r * (E k)ᴴ)).symm

lemma g79g_trace_isChannel {ι : Type} [Fintype ι] [DecidableEq ι] :
    IsChannel (fun r : Matrix ι ι ℂ => (fun _ _ : Fin 1 => r.trace)) := by
  have h := g79g_isChannel_of_kraus (fun (c : ι) => (Matrix.of fun (_ : Fin 1) (a : ι) => if a = c then (1:ℂ) else 0)) ?_
  · obtain ⟨m, E, hE, hr⟩ := h
    refine ⟨m, E, hE, fun r => ?_⟩
    rw [← hr]; ext i j
    simp [krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.trace, Matrix.conjTranspose_apply]
  · unfold IsKrausFamily; ext a b
    simp [Matrix.sum_apply, Matrix.mul_apply, Matrix.one_apply, Matrix.conjTranspose_apply]

lemma g79g_fin1_trace (M : Matrix (Fin 1) (Fin 1) ℂ) (i j : Fin 1) : M i j = M.trace := by
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]; simp [Matrix.trace]

lemma g79g_chan_fin1 {ι : Type} [Fintype ι] [DecidableEq ι] (Phi : Superop ι (Fin 1))
    (hPhi : IsChannel Phi) : Phi = (fun rho _ _ => rho.trace) := by
  obtain ⟨m, E, hE, hr⟩ := hPhi
  funext rho i j
  rw [hr, g79g_fin1_trace (krausApply E rho) i j]
  unfold krausApply
  rw [Matrix.trace_sum]
  simp_rw [Matrix.trace_mul_cycle (E _) rho]
  rw [← Matrix.trace_sum, ← Finset.sum_mul]
  unfold IsKrausFamily at hE
  rw [hE, Matrix.one_mul]

/-- Section 2.1, PDF p.7: unique scalar-output trace map, its rank and
canonical row-bra Kraus representation, with the corresponding identity complement. -/
theorem solution [Nonempty A] (Phi : Superop A (Fin 1))
    (hPhi : IsChannel Phi) :
    let H : A → Matrix (Fin 1) A ℂ := fun k _ a => if a = k then 1 else 0
    Phi = (fun rho _ _ => rho.trace) ∧ Phi = krausApply H ∧
    (choi Phi).rank = Fintype.card A ∧
    complementaryChannel (indexedKrausDilation H) = id ∧ (∃ envSize : ℕ, ∃ witness : Matrix (_ × Fin envSize) _ ℂ, receiverChannel witness = Phi ∧ IsAntidegradable witness) := by
  intro H
  have hT := g79g_chan_fin1 Phi hPhi
  have hH : krausApply H = (fun rho _ _ => rho.trace) := by
    have : H = fun k => Matrix.of (fun (_ : Fin 1) a => if a = k then (1:ℂ) else 0) := rfl
    rw [this]
    funext rho i j
    simp [krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.trace, Matrix.conjTranspose_apply]
  refine ⟨hT, hT.trans hH.symm, ?_, ?_, ?_⟩
  · have : choi Phi = 1 := by
      ext x y
      rw [hT]
      simp only [choi, Matrix.one_apply, Prod.ext_iff, Subsingleton.elim x.2 y.2]
      split_ifs with h
      · rw [h.1]; simp [Matrix.trace, Matrix.single_apply]
      · simp [Matrix.trace, Matrix.single_apply]; intro hh; exact absurd ⟨hh.symm, trivial⟩ h
    rw [this, Matrix.rank_one]; simp
  · funext rho; ext k k'
    simp [complementaryChannel, traceLeft, indexedKrausDilation, H, Matrix.mul_apply, Matrix.conjTranspose_apply]
  · set e := Fintype.equivFin A
    let W : Matrix (Fin 1 × Fin (Fintype.card A)) A ℂ :=
      Matrix.of fun be a => if a = e.symm be.2 then 1 else 0
    have hR : receiverChannel W = Phi := by
      rw [hT]; funext rho i j
      simp [W, receiverChannel, traceRight, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.trace]
      exact Equiv.sum_comp e.symm (fun a => rho a a)
    refine ⟨Fintype.card A, W, hR, ?_, fun r _ _ => r.trace, g79g_trace_isChannel, ?_⟩
    · ext a b
      simp [W, Matrix.mul_apply, Matrix.one_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type]
      rw [Equiv.sum_comp e.symm (fun c => if b = c then (if a = c then (1:ℂ) else 0) else 0)]
      simp [Finset.sum_ite_eq, eq_comm]
    · intro rho
      rw [hR, hT]; funext i j
      simp [W, complementaryChannel, traceLeft, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.trace]
      exact (Equiv.sum_comp e.symm (fun a => rho a a)).symm


end
