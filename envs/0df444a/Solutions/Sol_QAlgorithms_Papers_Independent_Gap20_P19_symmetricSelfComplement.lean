-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P19.symmetricSelfComplement
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T08:27:00.405223+00:00
-- url     : https://prove2.me/submissions/6976d089-974a-49b5-b540-d9668ce16269

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

lemma g79g_chan_smul {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] (D : Superop ι κ)
    (hD : IsChannel D) (c : ℂ) (X : Matrix ι ι ℂ) : D (c • X) = c • D X := by
  obtain ⟨m, E, _, h⟩ := hD
  rw [h, h]; simp [krausApply, Finset.smul_sum, Matrix.mul_smul, Matrix.smul_mul]

lemma g79g_chan_add {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] (D : Superop ι κ)
    (hD : IsChannel D) (X Y : Matrix ι ι ℂ) : D (X + Y) = D X + D Y := by
  obtain ⟨m, E, _, h⟩ := hD
  rw [h, h, h]; simp [krausApply, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]



lemma g79g_symm (p : Fin 3 × Fin 3) (k : Fin 6) : symmetricIsometry (p.2, p.1) k = symmetricIsometry p k := by
  obtain ⟨i, j⟩ := p
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [symmetricIsometry]

lemma g79g_s2 : ((Real.sqrt 2)⁻¹ : ℂ) * ((Real.sqrt 2)⁻¹ : ℂ) = 1/2 := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; push_cast; ring

lemma g79g_UUh (p q : Fin 3 × Fin 3) : (symmetricIsometry * symmetricIsometryᴴ) p q =
      (1/2 : ℂ)*((if p=q then 1 else 0)+(if p=(q.2,q.1) then 1 else 0)) := by
  obtain ⟨i, j⟩ := p
  obtain ⟨i', j'⟩ := q
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_six]
  fin_cases i <;> fin_cases j <;> fin_cases i' <;> fin_cases j' <;>
    simp [symmetricIsometry, g79g_s2] <;> ring

lemma g79g_iso : IsIsometry symmetricIsometry := by
  unfold IsIsometry
  ext k k'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type, Fin.sum_univ_three,
    Matrix.one_apply]
  fin_cases k <;> fin_cases k' <;> simp [symmetricIsometry, g79g_s2] <;> norm_num

lemma g79g_choi_eq {A B E : Type} [Fintype A] [DecidableEq A] [Fintype B] [Fintype E]
    (U : Matrix (B × E) A ℂ) :
    choi (receiverChannel U) = (Matrix.of fun (ab : A × B) (e : E) => U (ab.2, e) ab.1) *
      (Matrix.of fun (ab : A × B) (e : E) => U (ab.2, e) ab.1)ᴴ := by
  ext x y
  simp [choi, receiverChannel, traceRight, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.single_apply, Finset.sum_mul, Finset.mul_sum, ite_and]

lemma g79g_choi_rank {A B E : Type} [Fintype A] [DecidableEq A] [Fintype B] [Fintype E] [DecidableEq E]
    (U : Matrix (B × E) A ℂ) :
    (choi (receiverChannel U)).rank = ((Matrix.of fun (ab : A × B) (e : E) => U (ab.2, e) ab.1)ᴴ *
      (Matrix.of fun (ab : A × B) (e : E) => U (ab.2, e) ab.1)).rank := by
  rw [g79g_choi_eq, Matrix.rank_self_mul_conjTranspose, Matrix.rank_conjTranspose_mul_self]

lemma g79g_KK : ((Matrix.of fun (ab : Fin 6 × Fin 3) (e : Fin 3) => symmetricIsometry (ab.2, e) ab.1)ᴴ *
      (Matrix.of fun (ab : Fin 6 × Fin 3) (e : Fin 3) => symmetricIsometry (ab.2, e) ab.1)) =
      (2:ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  ext e e'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type, Fin.sum_univ_three,
    Fin.sum_univ_six, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply]
  fin_cases e <;> fin_cases e' <;> simp [symmetricIsometry, g79g_s2] <;> norm_num

lemma g79g_idChan {ι : Type} [Fintype ι] [DecidableEq ι] : IsChannel (fun r : Matrix ι ι ℂ => r) :=
  ⟨1, fun _ => 1, by simp [IsKrausFamily], fun r => by simp [krausApply]⟩


/-- Section 2.3, PDF p.11, (23): the constructed symmetric-subspace map
has equal marginals and is both classes; its Choi rank is three. -/
theorem solution :
    IsIsometry symmetricIsometry ∧
    (∀ p q, (symmetricIsometry * symmetricIsometryᴴ) p q =
      (1/2 : ℂ)*((if p=q then 1 else 0)+(if p=(q.2,q.1) then 1 else 0))) ∧
    complementaryChannel symmetricIsometry = symmetricSubspaceMap ∧
    (∃ envSize : ℕ, ∃ witness : Matrix (_ × Fin envSize) _ ℂ, receiverChannel witness = symmetricSubspaceMap ∧ IsDegradable witness) ∧ (∃ envSize : ℕ, ∃ witness : Matrix (_ × Fin envSize) _ ℂ, receiverChannel witness = symmetricSubspaceMap ∧ IsAntidegradable witness) ∧
    (choi symmetricSubspaceMap).rank = 3 := by
  have hc : complementaryChannel symmetricIsometry = symmetricSubspaceMap := by
    funext rho; ext e e'
    simp only [complementaryChannel, symmetricSubspaceMap, receiverChannel, traceLeft, traceRight,
      Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    have h1 := g79g_symm (b, e)
    have h2 := g79g_symm (b, e')
    simp only at h1 h2
    simp only [h1, h2]
  refine ⟨g79g_iso, g79g_UUh, hc, ⟨3, symmetricIsometry, rfl, g79g_iso, fun r => r, g79g_idChan, ?_⟩,
    ⟨3, symmetricIsometry, rfl, g79g_iso, fun r => r, g79g_idChan, ?_⟩, ?_⟩
  · intro rho; rw [hc]; rfl
  · intro rho; rw [hc]; rfl
  · unfold symmetricSubspaceMap
    rw [g79g_choi_rank, g79g_KK]
    rw [Matrix.rank_of_isUnit]
    · simp
    · rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_smul, Matrix.det_one]; simp



end
