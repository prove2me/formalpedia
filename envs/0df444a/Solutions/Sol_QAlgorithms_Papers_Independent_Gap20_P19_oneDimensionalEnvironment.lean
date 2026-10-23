-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P19.oneDimensionalEnvironment
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T08:50:13.422437+00:00
-- url     : https://prove2.me/submissions/a4fc35ce-209a-4708-b351-a1d3779d1d03

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


lemma g79g_trace_isChannel {ι : Type} [Fintype ι] [DecidableEq ι] :
    IsChannel (fun r : Matrix ι ι ℂ => (fun _ _ : Fin 1 => r.trace)) := by
  have h := g79g_isChannel_of_kraus (fun (c : ι) => (Matrix.of fun (_ : Fin 1) (a : ι) => if a = c then (1:ℂ) else 0)) ?_
  · obtain ⟨m, E, hE, hr⟩ := h
    refine ⟨m, E, hE, fun r => ?_⟩
    rw [← hr]; ext i j
    simp [krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.trace, Matrix.conjTranspose_apply]
  · unfold IsKrausFamily; ext a b
    simp [Matrix.sum_apply, Matrix.mul_apply, Matrix.one_apply, Matrix.conjTranspose_apply]

lemma g79g_choi_kraus {ι κ K : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [Fintype K]
    (H : K → Matrix κ ι ℂ) :
    choi (krausApply H) = (Matrix.of fun (ab : ι × κ) (k : K) => H k ab.2 ab.1) *
      (Matrix.of fun (ab : ι × κ) (k : K) => H k ab.2 ab.1)ᴴ := by
  ext x y
  simp [choi, krausApply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply,
    Matrix.single_apply, Finset.sum_mul, Finset.mul_sum, ite_and]

lemma g79g_rank_one_cols {m n : Type} [Fintype m] [Fintype n] [DecidableEq n] (K : Matrix m n ℂ)
    (h : K.rank = 1) : ∃ u : m → ℂ, ∃ c : n → ℂ, ∀ x k, K x k = c k * u x := by
  unfold Matrix.rank at h
  obtain ⟨u, -, hu⟩ := finrank_eq_one_iff'.mp h
  have hu' : ∀ k, ∃ c : ℂ, c • u = ⟨K *ᵥ Pi.single k 1, LinearMap.mem_range_self _ _⟩ :=
    fun k => hu _
  choose c hc using hu'
  refine ⟨(u : m → ℂ), c, fun x k => ?_⟩
  have h2 := congrFun (congrArg Subtype.val (hc k)) x
  simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul, Matrix.mulVec_single_one] at h2
  calc K x k = K.col k x := rfl
    _ = _ := h2.symm

/-- Section 2.1, PDF p.7: minimum environment dimension one gives an isometry,
trace complement, and the explicit trace degrader. -/
theorem solution [Nonempty A] [Nonempty B]
    (Phi : Superop A B) (hPhi : IsChannel Phi) (hrank : (choi Phi).rank = 1) :
    Fintype.card A ≤ Fintype.card B ∧ (∃ envSize : ℕ, ∃ witness : Matrix (_ × Fin envSize) _ ℂ, receiverChannel witness = Phi ∧ IsDegradable witness) ∧
    ∃ V : Matrix B A ℂ, IsIsometry V ∧ Phi = conjSuperop V ∧
      let U : Matrix (B × Fin 1) A ℂ := fun be a => V be.1 a
      complementaryChannel U = (fun rho _ _ => rho.trace) ∧
      IsChannel (fun rho : Matrix B B ℂ => (fun _ _ : Fin 1 => rho.trace)) ∧
      (∀ rho, (Phi rho).trace = rho.trace) := by
  obtain ⟨m, E, hE, hPE⟩ := id hPhi
  have hPk : Phi = krausApply E := funext hPE
  have hK1 : (Matrix.of fun (ab : A × B) (k : Fin m) => E k ab.2 ab.1).rank = 1 := by
    rw [← Matrix.rank_self_mul_conjTranspose, ← g79g_choi_kraus, ← hPk, hrank]
  obtain ⟨u, c, huc⟩ := g79g_rank_one_cols _ hK1
  let M : Matrix B A ℂ := Matrix.of fun b a => u (a, b)
  have hEk : ∀ k, E k = c k • M := by
    intro k; ext b a; have := huc (a, b) k; simp only [Matrix.of_apply] at this; simp [M, this]
  set s : ℝ := ∑ k, ‖c k‖^2 with hs
  have hcc : ∀ k, c k * conj (c k) = ((‖c k‖^2 : ℝ) : ℂ) := by
    intro k; rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hMM : (s : ℂ) • (Mᴴ * M) = 1 := by
    unfold IsKrausFamily at hE
    rw [← hE]; simp_rw [hEk, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [hs, Complex.ofReal_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hcc, mul_comm]; rfl
  have hspos : 0 ≤ s := Finset.sum_nonneg fun k _ => by positivity
  let V : Matrix B A ℂ := (Real.sqrt s : ℂ) • M
  have hVV : IsIsometry V := by
    unfold IsIsometry
    simp only [V, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [← hMM, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt hspos]
  have hPV : Phi = conjSuperop V := by
    rw [hPk]; funext rho
    simp only [krausApply, conjSuperop, hEk, V, Matrix.conjTranspose_smul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul]
    rw [← Finset.sum_smul, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt hspos, hs, Complex.ofReal_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm, hcc]
  have htr : ∀ rho : Matrix A A ℂ, (V * rho * Vᴴ).trace = rho.trace := by
    intro rho
    rw [Matrix.trace_mul_cycle, hVV, Matrix.one_mul]
  let U : Matrix (B × Fin 1) A ℂ := Matrix.of fun be a => V be.1 a
  have hUR : receiverChannel U = Phi := by
    rw [hPV]; funext rho; ext b b'
    simp [receiverChannel, traceRight, conjSuperop, U, Matrix.mul_apply]
  have hUC : complementaryChannel U = (fun rho _ _ => rho.trace) := by
    funext rho i j
    rw [← htr rho]
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
    simp [complementaryChannel, traceLeft, U, Matrix.mul_apply, Matrix.trace]
  have hUiso : IsIsometry U := by
    unfold IsIsometry at *
    rw [← hVV]; ext a a'
    simp [U, Matrix.mul_apply, Fintype.sum_prod_type]
  refine ⟨?_, ⟨1, U, hUR, hUiso, fun r _ _ => r.trace, g79g_trace_isChannel, ?_⟩, V, hVV, hPV, hUC,
    g79g_trace_isChannel, ?_⟩
  · have h1 : (Vᴴ * V).rank = Fintype.card A := by rw [hVV, Matrix.rank_one]
    calc Fintype.card A = (Vᴴ * V).rank := h1.symm
      _ ≤ V.rank := Matrix.rank_mul_le_right _ _
      _ ≤ Fintype.card B := Matrix.rank_le_card_height V
  · intro rho; rw [hUC, hUR, hPV]; simp only [conjSuperop]; rw [htr]
  · intro rho; rw [hPV]; exact htr rho



end
