-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P19.antidegradableConvex
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T08:17:59.210334+00:00
-- url     : https://prove2.me/submissions/5ea89d05-a68b-40e6-94e3-dbe0bda3c20c

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


lemma g79g_sq (x : ℝ) (hx : 0 ≤ x) : (Real.sqrt x : ℂ) * conj (Real.sqrt x : ℂ) = (x : ℂ) := by
  rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt hx]

lemma g79g_smul_conj {ι κ : Type} [Fintype ι] (c : ℂ) (M : Matrix κ ι ℂ) (X : Matrix ι ι ℂ) :
    (c • M) * X * (c • M)ᴴ = (c * conj c) • (M * X * Mᴴ) := by
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rfl

lemma g79g_smul_conj' {ι κ : Type} [Fintype κ] (c : ℂ) (M : Matrix κ ι ℂ) :
    (c • M)ᴴ * (c • M) = (c * conj c) • (Mᴴ * M) := by
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm]
  rfl

/-- Theorem 18, PDF p.27: convexity, including p=0 and p=1. -/
theorem solution [Nonempty A] [Nonempty B]
    (Phi Psi : Superop A B) (hPhi : (∃ envSize : ℕ, ∃ witness : Matrix (_ × Fin envSize) _ ℂ, receiverChannel witness = Phi ∧ IsAntidegradable witness)) (hPsi : (∃ envSize : ℕ, ∃ witness : Matrix (_ × Fin envSize) _ ℂ, receiverChannel witness = Psi ∧ IsAntidegradable witness))
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (∃ envSize : ℕ, ∃ witness : Matrix (_ × Fin envSize) _ ℂ, receiverChannel witness = (fun rho => (p : ℂ) • Phi rho + ((1-p : ℝ) : ℂ) • Psi rho) ∧ IsAntidegradable witness) := by
  obtain ⟨n1, W1, hW1, hW1iso, D1, hD1, hDW1⟩ := hPhi
  obtain ⟨n2, W2, hW2, hW2iso, D2, hD2, hDW2⟩ := hPsi
  set e := (finSumFinEquiv : Fin n1 ⊕ Fin n2 ≃ Fin (n1+n2))
  set S : Fin n1 ⊕ Fin n2 → Matrix B A ℂ :=
    Sum.elim (fun k => (Real.sqrt p : ℂ) • g79g_slice W1 k)
      (fun k => (Real.sqrt (1-p) : ℂ) • g79g_slice W2 k) with hSdef
  let V : Matrix (B × Fin (n1+n2)) A ℂ := Matrix.of fun bt a => S (e.symm bt.2) bt.1 a
  have hs : ∀ t, g79g_slice V t = S (e.symm t) := by
    intro t; ext c a; rfl
  have h1p : 0 ≤ 1 - p := by linarith
  have hR : receiverChannel V = (fun rho => (p : ℂ) • Phi rho + ((1-p : ℝ) : ℂ) • Psi rho) := by
    funext rho
    rw [← hW1, ← hW2, g79g_recv_eq, g79g_recv_eq, g79g_recv_eq]
    simp_rw [hs]
    rw [← Equiv.sum_comp e (fun t => S (e.symm t) * rho * (S (e.symm t))ᴴ)]
    simp only [Equiv.symm_apply_apply, Fintype.sum_sum_type, hSdef, Sum.elim_inl, Sum.elim_inr,
      g79g_smul_conj, g79g_sq p hp0, g79g_sq (1-p) h1p, Finset.smul_sum]
  let P1 : Matrix (Fin n1) (Fin (n1+n2)) ℂ := Matrix.of fun k t => if t = e (Sum.inl k) then 1 else 0
  let P2 : Matrix (Fin n2) (Fin (n1+n2)) ℂ := Matrix.of fun k t => if t = e (Sum.inr k) then 1 else 0
  have hP1 : ∀ r : Matrix (Fin (n1+n2)) (Fin (n1+n2)) ℂ, P1 * r * P1ᴴ =
      Matrix.of fun k k' => r (e (Sum.inl k)) (e (Sum.inl k')) := by
    intro r; ext k k'; simp [P1, Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hP2 : ∀ r : Matrix (Fin (n1+n2)) (Fin (n1+n2)) ℂ, P2 * r * P2ᴴ =
      Matrix.of fun k k' => r (e (Sum.inr k)) (e (Sum.inr k')) := by
    intro r; ext k k'; simp [P2, Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hPP : P1ᴴ * P1 + P2ᴴ * P2 = 1 := by
    ext t t'
    simp only [P1, P2, Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Matrix.one_apply]
    obtain ⟨u, rfl⟩ := e.surjective t
    obtain ⟨u', rfl⟩ := e.surjective t'
    rcases u with u | u <;> rcases u' with u' | u' <;> simp [Finset.sum_ite_eq']
  have hDc : IsChannel (fun r : Matrix (Fin (n1+n2)) (Fin (n1+n2)) ℂ =>
      D1 (Matrix.of fun k k' => r (e (Sum.inl k)) (e (Sum.inl k'))) +
      D2 (Matrix.of fun k k' => r (e (Sum.inr k)) (e (Sum.inr k')))) := by
    obtain ⟨m1, E1, hE1, h1⟩ := id hD1
    obtain ⟨m2, E2, hE2, h2⟩ := id hD2
    have := g79g_isChannel_of_kraus
      (Sum.elim (fun i => E1 i * P1) (fun i => E2 i * P2)) ?_
    · obtain ⟨q, G, hG, hr⟩ := this
      refine ⟨q, G, hG, fun r => ?_⟩
      rw [← hr]
      show D1 _ + D2 _ = _
      rw [← hP1 r, ← hP2 r, h1, h2]
      simp only [krausApply, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Matrix.conjTranspose_mul,
        Matrix.mul_assoc]
    · unfold IsKrausFamily at *
      rw [Fintype.sum_sum_type, ← hPP]
      simp only [Sum.elim_inl, Sum.elim_inr]
      congr 1
      · have : ∀ i, (E1 i * P1)ᴴ * (E1 i * P1) = P1ᴴ * ((E1 i)ᴴ * E1 i) * P1 := by
          intro i; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        rw [Finset.sum_congr rfl fun i _ => this i, ← Matrix.sum_mul, ← Matrix.mul_sum, hE1, Matrix.mul_one]
      · have : ∀ i, (E2 i * P2)ᴴ * (E2 i * P2) = P2ᴴ * ((E2 i)ᴴ * E2 i) * P2 := by
          intro i; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        rw [Finset.sum_congr rfl fun i _ => this i, ← Matrix.sum_mul, ← Matrix.mul_sum, hE2, Matrix.mul_one]
  refine ⟨n1+n2, V, hR, ?_, _, hDc, ?_⟩
  · unfold IsIsometry at *
    rw [g79g_iso_eq] at hW1iso hW2iso ⊢
    simp_rw [hs]
    rw [← Equiv.sum_comp e (fun t => (S (e.symm t))ᴴ * S (e.symm t))]
    simp only [Equiv.symm_apply_apply, Fintype.sum_sum_type, hSdef, Sum.elim_inl, Sum.elim_inr,
      g79g_smul_conj', g79g_sq p hp0, g79g_sq (1-p) h1p, ← Finset.smul_sum, hW1iso, hW2iso]
    rw [← add_smul]; push_cast; simp
  · intro rho
    rw [hR]
    have e1 : (Matrix.of fun k k' => complementaryChannel V rho (e (Sum.inl k)) (e (Sum.inl k'))) =
        (p : ℂ) • complementaryChannel W1 rho := by
      ext k k'
      simp only [Matrix.of_apply, g79g_comp_eq, hs, Equiv.symm_apply_apply, hSdef, Sum.elim_inl,
        Matrix.smul_apply]
      rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.trace_smul, Matrix.trace_smul, smul_smul, ← g79g_sq p hp0]
      rfl
    have e2 : (Matrix.of fun k k' => complementaryChannel V rho (e (Sum.inr k)) (e (Sum.inr k'))) =
        ((1-p : ℝ) : ℂ) • complementaryChannel W2 rho := by
      ext k k'
      simp only [Matrix.of_apply, g79g_comp_eq, hs, Equiv.symm_apply_apply, hSdef, Sum.elim_inr,
        Matrix.smul_apply]
      rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.trace_smul, Matrix.trace_smul, smul_smul, ← g79g_sq (1-p) h1p]
      rfl
    simp only
    rw [e1, e2, g79g_chan_smul _ hD1, g79g_chan_smul _ hD2, ← hDW1, ← hDW2, hW1, hW2]



end
