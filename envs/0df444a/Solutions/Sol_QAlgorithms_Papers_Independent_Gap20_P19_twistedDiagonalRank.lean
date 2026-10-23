-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P19.twistedDiagonalRank
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T08:42:11.508463+00:00
-- url     : https://prove2.me/submissions/0b359f38-49c1-4ddf-bcc5-67cdf360a439

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


lemma g79g_choi_kraus {ι κ K : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [Fintype K]
    (H : K → Matrix κ ι ℂ) :
    choi (krausApply H) = (Matrix.of fun (ab : ι × κ) (k : K) => H k ab.2 ab.1) *
      (Matrix.of fun (ab : ι × κ) (k : K) => H k ab.2 ab.1)ᴴ := by
  ext x y
  simp [choi, krausApply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply,
    Matrix.single_apply, Finset.sum_mul, Finset.mul_sum, ite_and]

lemma g79g_kraus_pure {ι κ K : Type} [Fintype ι] [Fintype κ] [Fintype K]
    (H : K → Matrix κ ι ℂ) (ψ : EuclideanSpace ℂ ι) :
    krausApply H (pureDensity ψ) = (Matrix.of fun (b : κ) (k : K) => ∑ a, H k b a * ψ a) *
      (Matrix.of fun (b : κ) (k : K) => ∑ a, H k b a * ψ a)ᴴ := by
  ext b b'
  simp [krausApply, pureDensity, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply,
    Finset.sum_mul, Finset.mul_sum, map_sum, mul_assoc, mul_comm, mul_left_comm]

lemma g79g_rank_leftinv {m n o : Type} [Fintype m] [Fintype n] [Fintype o] [DecidableEq n]
    (L : Matrix n m ℂ) (N : Matrix m n ℂ) (V : Matrix n o ℂ) (h : L * N = 1) :
    (N * V).rank = V.rank := by
  apply le_antisymm (Matrix.rank_mul_le_right _ _)
  calc V.rank = (L * (N * V)).rank := by rw [← Matrix.mul_assoc, h, Matrix.one_mul]
    _ ≤ (N * V).rank := Matrix.rank_mul_le_right _ _

/-- Theorem 12, PDF pp.19–20. Corrected printed output rank d_B to d_E:
(54) computes d_E, and the identity channel disproves the printed d_B clause. -/
theorem solution [Nonempty A] (Phi : Superop A A)
    (hPhi : IsChannel Phi) (htwist : TwistedDiagonal Phi) :
    (choi Phi).rank ≤ Fintype.card A ∧
    ∃ psi : EuclideanSpace ℂ A, IsState psi ∧
      (Phi (pureDensity psi)).rank = (choi Phi).rank := by
  obtain ⟨m, H, hH, rfl, X, Y, hX, hY, hD⟩ := htwist
  choose v hv using hD
  have hXd := (Matrix.isUnit_iff_isUnit_det X).1 hX
  have hYd := (Matrix.isUnit_iff_isUnit_det Y).1 hY
  have hXi : X * X⁻¹ = 1 := Matrix.mul_nonsing_inv X hXd
  have hXi' : X⁻¹ * X = 1 := Matrix.nonsing_inv_mul X hXd
  have hYi : Y * Y⁻¹ = 1 := Matrix.mul_nonsing_inv Y hYd
  have hYi' : Y⁻¹ * Y = 1 := Matrix.nonsing_inv_mul Y hYd
  have hHk : ∀ k, H k = Y⁻¹ * Matrix.diagonal (v k) * X⁻¹ := by
    intro k; rw [← hv k, Matrix.mul_assoc, Matrix.mul_assoc, hXi, Matrix.mul_one, ← Matrix.mul_assoc,
      hYi', Matrix.one_mul]
  let V : Matrix A (Fin m) ℂ := Matrix.of fun c k => v k c
  let N : Matrix (A × A) A ℂ := Matrix.of fun ab c => Y⁻¹ ab.2 c * X⁻¹ c ab.1
  let L : Matrix A (A × A) ℂ := Matrix.of fun c ab => X ab.1 c * Y c ab.2
  have hLN : L * N = 1 := by
    ext c c'
    have h1 : (L * N) c c' = (X⁻¹ * X) c' c * (Y * Y⁻¹) c c' := by
      simp only [L, N, Matrix.mul_apply, Matrix.of_apply, Fintype.sum_prod_type, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
    rw [h1, hXi', hYi, Matrix.one_apply, Matrix.one_apply]
    by_cases h : c = c' <;> simp [h, eq_comm]
  have hK : (Matrix.of fun (ab : A × A) (k : Fin m) => H k ab.2 ab.1) = N * V := by
    ext ab k
    simp only [hHk, Matrix.mul_diagonal, Matrix.of_apply, Matrix.mul_apply, N, V]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  have hrank : (choi (krausApply H)).rank = V.rank := by
    rw [g79g_choi_kraus, hK, Matrix.rank_self_mul_conjTranspose, g79g_rank_leftinv L N V hLN]
  refine ⟨by rw [hrank]; exact Matrix.rank_le_card_height V, ?_⟩
  obtain ⟨ψ0, hψ0⟩ : ∃ ψ0 : EuclideanSpace ℂ A, ψ0 = WithLp.toLp 2 (X *ᵥ (fun _ => 1)) := ⟨_, rfl⟩
  have hψ0ne : ψ0 ≠ 0 := by
    intro h
    have h2 : X *ᵥ (fun _ : A => (1:ℂ)) = 0 := by
      have := congrArg (WithLp.ofLp) h; simpa [hψ0] using this
    have h3 := congrArg (fun w => X⁻¹ *ᵥ w) h2
    simp only [Matrix.mulVec_mulVec, hXi', Matrix.one_mulVec, Matrix.mulVec_zero] at h3
    have := congrFun h3 (Classical.arbitrary A)
    simp at this
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = ((‖ψ0‖ : ℝ) : ℂ)⁻¹ := ⟨_, rfl⟩
  refine ⟨c • ψ0, by rw [hc]; exact norm_smul_inv_norm hψ0ne, ?_⟩
  rw [hrank, g79g_kraus_pure]
  have hvec : ∀ k, (fun b => ∑ a, H k b a * (c • ψ0) a) = Y⁻¹ *ᵥ (c • v k) := by
    intro k
    have hw : (fun a => (c • ψ0) a) = c • (X *ᵥ fun _ => (1:ℂ)) := by ext a; simp [hψ0]
    have : (fun b => ∑ a, H k b a * (c • ψ0) a) = H k *ᵥ (fun a => (c • ψ0) a) := by
      ext b; simp [Matrix.mulVec, dotProduct]
    rw [this, hw, hHk, ← Matrix.mulVec_mulVec, Matrix.mulVec_smul, Matrix.mulVec_mulVec (M := X⁻¹) (N := X), hXi',
      Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
    congr 1; ext d; simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply, mul_comm]
  have hG : (Matrix.of fun (b : A) (k : Fin m) => ∑ a, H k b a * (c • ψ0) a) = (c • Y⁻¹) * V := by
    ext b k
    have := congrFun (hvec k) b
    rw [Matrix.of_apply, this]
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, V, mul_assoc, mul_left_comm]
  rw [hG, Matrix.rank_self_mul_conjTranspose, Matrix.rank_mul_eq_right_of_isUnit_det]
  rw [Matrix.det_smul]
  refine IsUnit.mul (IsUnit.pow _ ?_) (Matrix.isUnit_nonsing_inv_det Y hYd)
  rw [hc, isUnit_iff_ne_zero]
  have : ‖ψ0‖ ≠ 0 := norm_ne_zero_iff.mpr hψ0ne
  exact inv_ne_zero (Complex.ofReal_ne_zero.mpr this)



end
