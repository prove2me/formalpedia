-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P19.antidegradablePostprocessing
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T08:14:20.354749+00:00
-- url     : https://prove2.me/submissions/31d6d42f-2336-4e7f-a772-d3f3335b9149

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

lemma g79g_isChannel_comp {ι κ μ : Type} [Fintype ι] [Fintype κ] [Fintype μ] [DecidableEq ι]
    [DecidableEq κ] (Phi : Superop ι κ) (Psi : Superop κ μ) (h1 : IsChannel Phi)
    (h2 : IsChannel Psi) : IsChannel (fun r => Psi (Phi r)) := by
  obtain ⟨m, E, hE, hPhi⟩ := h1
  obtain ⟨m', F, hF, hPsi⟩ := h2
  have := g79g_isChannel_of_kraus (fun p : Fin m' × Fin m => F p.1 * E p.2) ?_
  · obtain ⟨n, G, hG, hr⟩ := this
    refine ⟨n, G, hG, fun r => ?_⟩
    show Psi (Phi r) = _
    rw [← hr, hPhi, hPsi]
    simp only [krausApply, Fintype.sum_prod_type, Matrix.conjTranspose_mul, Matrix.mul_sum,
      Matrix.sum_mul, Matrix.mul_assoc]
  · unfold IsKrausFamily at *
    rw [Fintype.sum_prod_type, Finset.sum_comm, ← hE]
    refine Finset.sum_congr rfl fun j _ => ?_
    have : ∀ i, (F i * E j)ᴴ * (F i * E j) = (E j)ᴴ * ((F i)ᴴ * F i) * E j := by
      intro i; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [Finset.sum_congr rfl fun i _ => this i, ← Matrix.sum_mul, ← Matrix.mul_sum]
    rw [hF, Matrix.mul_one]

def g79g_slice {A B E : Type} (U : Matrix (B × E) A ℂ) (k : E) : Matrix B A ℂ :=
  Matrix.of fun b a => U (b,k) a

lemma g79g_recv_eq {A B E : Type} [Fintype A] [Fintype B] [Fintype E] (U : Matrix (B × E) A ℂ)
    (rho : Matrix A A ℂ) :
    receiverChannel U rho = ∑ k, g79g_slice U k * rho * (g79g_slice U k)ᴴ := by
  ext b b'
  simp [receiverChannel, traceRight, g79g_slice, Matrix.mul_apply, Matrix.sum_apply,
    Matrix.conjTranspose_apply]

lemma g79g_comp_eq {A B E : Type} [Fintype A] [Fintype B] [Fintype E] (U : Matrix (B × E) A ℂ)
    (rho : Matrix A A ℂ) (k k' : E) :
    complementaryChannel U rho k k' = (g79g_slice U k * rho * (g79g_slice U k')ᴴ).trace := by
  simp [complementaryChannel, traceLeft, g79g_slice, Matrix.mul_apply, Matrix.trace,
    Matrix.conjTranspose_apply]

lemma g79g_iso_eq {A B E : Type} [Fintype A] [Fintype B] [Fintype E] (U : Matrix (B × E) A ℂ) :
    Uᴴ * U = ∑ k, (g79g_slice U k)ᴴ * g79g_slice U k := by
  ext a a'
  simp [g79g_slice, Matrix.mul_apply, Matrix.sum_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type]
  exact Finset.sum_comm

lemma g79g_trace_kraus {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] {m : ℕ}
    (F : Fin m → Matrix κ ι ℂ) (hF : IsKrausFamily F) (X : Matrix ι ι ℂ) :
    ∑ j, (F j * X * (F j)ᴴ).trace = X.trace := by
  simp_rw [Matrix.trace_mul_cycle (F _) X]
  rw [← Matrix.trace_sum, ← Matrix.sum_mul]
  unfold IsKrausFamily at hF
  rw [hF, Matrix.one_mul]

lemma g79g_partial_isChannel (n m : ℕ) :
    IsChannel (fun r : Matrix (Fin (n*m)) (Fin (n*m)) ℂ =>
      Matrix.of fun k k' : Fin n => ∑ j : Fin m, r (finProdFinEquiv (k,j)) (finProdFinEquiv (k',j))) := by
  set e := (finProdFinEquiv : Fin n × Fin m ≃ Fin (n*m))
  have h := g79g_isChannel_of_kraus
    (fun j : Fin m => (Matrix.of fun (k : Fin n) (t : Fin (n*m)) => if t = e (k,j) then (1:ℂ) else 0)) ?_
  · obtain ⟨p, G, hG, hr⟩ := h
    refine ⟨p, G, hG, fun r => ?_⟩
    rw [← hr]; ext k k'
    simp [krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  · unfold IsKrausFamily; ext t t'
    simp [Matrix.sum_apply, Matrix.mul_apply, Matrix.one_apply, Matrix.conjTranspose_apply]
    rw [Finset.sum_comm, ← Fintype.sum_prod_type'
      (f := fun j c => if t' = e (j, c) then (if t = e (j, c) then (1:ℂ) else 0) else 0),
      Equiv.sum_comp e (fun s => if t' = s then (if t = s then (1:ℂ) else 0) else 0)]
    simp [Finset.sum_ite_eq, eq_comm]

/-- Lemma 17, PDF p.27: arbitrary CPTP postprocessing and dimensions. -/
theorem solution [Nonempty A] [Nonempty B] [Nonempty C]
    (Gamma : Superop A B) (Delta : Superop B C)
    (hGamma : (∃ envSize : ℕ, ∃ witness : Matrix (_ × Fin envSize) _ ℂ, receiverChannel witness = Gamma ∧ IsAntidegradable witness)) (hDelta : IsChannel Delta) :
    (∃ envSize : ℕ, ∃ witness : Matrix (_ × Fin envSize) _ ℂ, receiverChannel witness = (Delta ∘ Gamma) ∧ IsAntidegradable witness) := by
  obtain ⟨n, W, hW, hWiso, D, hD, hDW⟩ := hGamma
  obtain ⟨m, F, hF, hDelta'⟩ := hDelta
  set e := (finProdFinEquiv : Fin n × Fin m ≃ Fin (n*m))
  let V : Matrix (C × Fin (n*m)) A ℂ :=
    Matrix.of fun ct a => (F (e.symm ct.2).2 * g79g_slice W (e.symm ct.2).1) ct.1 a
  have hs : ∀ t, g79g_slice V t = F (e.symm t).2 * g79g_slice W (e.symm t).1 := by
    intro t; ext c a; rfl
  have hR : receiverChannel V = Delta ∘ Gamma := by
    funext rho
    show _ = Delta (Gamma rho)
    rw [← hW, hDelta', g79g_recv_eq, g79g_recv_eq]
    simp_rw [hs]
    rw [← Equiv.sum_comp e (fun t => F (e.symm t).2 * g79g_slice W (e.symm t).1 * rho *
      (F (e.symm t).2 * g79g_slice W (e.symm t).1)ᴴ)]
    simp only [Equiv.symm_apply_apply, krausApply, Fintype.sum_prod_type, Matrix.mul_sum,
      Matrix.sum_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    exact Finset.sum_comm
  refine ⟨n*m, V, hR, ?_, fun r => Delta (D (Matrix.of fun k k' : Fin n =>
      ∑ j : Fin m, r (e (k,j)) (e (k',j)))), ?_, ?_⟩
  · unfold IsIsometry at *
    rw [g79g_iso_eq] at hWiso ⊢
    rw [← hWiso]
    simp_rw [hs]
    rw [← Equiv.sum_comp e (fun t => (F (e.symm t).2 * g79g_slice W (e.symm t).1)ᴴ *
      (F (e.symm t).2 * g79g_slice W (e.symm t).1))]
    simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ => ?_
    have : ∀ j, (F j * g79g_slice W k)ᴴ * (F j * g79g_slice W k) =
        (g79g_slice W k)ᴴ * ((F j)ᴴ * F j) * g79g_slice W k := by
      intro j; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [Finset.sum_congr rfl fun j _ => this j, ← Matrix.sum_mul, ← Matrix.mul_sum, hF, Matrix.mul_one]
  · exact g79g_isChannel_comp _ _ (g79g_isChannel_comp _ _ (g79g_partial_isChannel n m) hD) ⟨m, F, hF, hDelta'⟩
  · intro rho
    rw [hR]
    show Delta (Gamma rho) = _
    rw [← hW, hDW]
    congr 2
    ext k k'
    simp only [Matrix.of_apply, g79g_comp_eq, hs, Equiv.symm_apply_apply]
    rw [← g79g_trace_kraus F hF]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]



end
