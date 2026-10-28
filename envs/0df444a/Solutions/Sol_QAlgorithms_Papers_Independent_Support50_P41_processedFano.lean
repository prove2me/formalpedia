-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P41.processedFano
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T07:24:56.156435+00:00
-- url     : https://prove2.me/submissions/c516cd4f-7f64-46e7-b2f4-a5083112a822

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P41

-- ===== KFA =====

/-! Generic: two families with equal Gram data are related by a unitary matrix. -/

noncomputable section

namespace X4KF
open scoped Matrix ComplexConjugate InnerProductSpace

variable {P : Type*} [Fintype P]

/-- equal Gram data ⇒ a linear isometry of the whole space sends `β` to `α`. -/
lemma gram_iso {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (α β : P → V) (h : ∀ p q, ⟪β p, β q⟫_ℂ = ⟪α p, α q⟫_ℂ) :
    ∃ T : V →ₗᵢ[ℂ] V, ∀ p, T (β p) = α p := by
  classical
  let F : (P → ℂ) →ₗ[ℂ] V := Fintype.linearCombination ℂ β
  let G : (P → ℂ) →ₗ[ℂ] V := Fintype.linearCombination ℂ α
  have hinner : ∀ c c' : P → ℂ, ⟪F c, F c'⟫_ℂ = ⟪G c, G c'⟫_ℂ := by
    intro c c'
    simp only [F, G, Fintype.linearCombination_apply, sum_inner, inner_sum, inner_smul_left,
      inner_smul_right, h]
  have hnorm : ∀ c, ‖G c‖ = ‖F c‖ := by
    intro c
    have h1 := hinner c c
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h1
    have h2 : ‖F c‖ ^ 2 = ‖G c‖ ^ 2 := by exact_mod_cast h1
    nlinarith [norm_nonneg (F c), norm_nonneg (G c), sq_nonneg (‖F c‖ - ‖G c‖),
      sq_nonneg (‖F c‖ + ‖G c‖)]
  have hker : LinearMap.ker F ≤ LinearMap.ker G := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    rw [← norm_eq_zero, hnorm, hc, norm_zero]
  let L0 : LinearMap.range F →ₗ[ℂ] V :=
    ((LinearMap.ker F).liftQ G hker).comp F.quotKerEquivRange.symm.toLinearMap
  have hL0 : ∀ c, L0 ⟨F c, LinearMap.mem_range_self F c⟩ = G c := by
    intro c
    simp only [L0, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
    have : F.quotKerEquivRange.symm ⟨F c, LinearMap.mem_range_self F c⟩ =
        (LinearMap.ker F).mkQ c := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    rw [this]
    rfl
  let L : LinearMap.range F →ₗᵢ[ℂ] V :=
    { toLinearMap := L0
      norm_map' := by
        rintro ⟨x, c, rfl⟩
        change ‖L0 ⟨F c, LinearMap.mem_range_self F c⟩‖ = ‖F c‖
        rw [hL0, hnorm] }
  refine ⟨L.extend, fun p => ?_⟩
  have hb : β p = F (Pi.single p 1) := by
    simp [F, Fintype.linearCombination_apply_single]
  have ha : α p = G (Pi.single p 1) := by
    simp [G, Fintype.linearCombination_apply_single]
  have := LinearIsometry.extend_apply L ⟨F (Pi.single p 1), LinearMap.mem_range_self F _⟩
  rw [hb, ha]
  change L.extend ((⟨F (Pi.single p 1), LinearMap.mem_range_self F _⟩ : LinearMap.range F) : V) = _
  rw [this]
  exact hL0 _

/-- matrix form on `EuclideanSpace ℂ (Fin L)`: equal Gram data ⇒ `α p = U β p` for a unitary `U`. -/
lemma gram_unitary {L : ℕ} [DecidableEq (Fin L)] (α β : P → Fin L → ℂ)
    (h : ∀ p q, ∑ l, conj (β p l) * β q l = ∑ l, conj (α p l) * α q l) :
    ∃ U : Matrix.unitaryGroup (Fin L) ℂ, ∀ p k,
      α p k = ∑ l, (U : Matrix (Fin L) (Fin L) ℂ) k l * β p l := by
  have hin : ∀ x y : Fin L → ℂ, ⟪(WithLp.toLp 2 x : EuclideanSpace ℂ (Fin L)), WithLp.toLp 2 y⟫_ℂ =
      ∑ l, conj (x l) * y l := by
    intro x y
    simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]
  obtain ⟨T, hT⟩ := gram_iso (V := EuclideanSpace ℂ (Fin L)) (fun p => WithLp.toLp 2 (α p))
    (fun p => WithLp.toLp 2 (β p)) (by
      intro p q
      rw [hin, hin, h])
  let U : Matrix (Fin L) (Fin L) ℂ := fun k l => T (EuclideanSpace.single l 1) k
  have hcol : ∀ l l', ∑ k, conj (U k l) * U k l' = if l = l' then 1 else 0 := by
    intro l l'
    have := T.inner_map_map (EuclideanSpace.single l (1 : ℂ)) (EuclideanSpace.single l' 1)
    have e1 := hin (T (EuclideanSpace.single l (1 : ℂ))).ofLp (T (EuclideanSpace.single l' (1 : ℂ))).ofLp
    simp only [WithLp.toLp_ofLp] at e1
    rw [e1] at this
    simp only [U]
    rw [this, EuclideanSpace.inner_single_left]
    simp [PiLp.single_apply]
  have hU : star U * U = 1 := by
    ext l l'
    simp only [Matrix.mul_apply, Matrix.star_apply, RCLike.star_def, Matrix.one_apply]
    exact hcol l l'
  refine ⟨⟨U, Matrix.mem_unitaryGroup_iff'.mpr hU⟩, fun p k => ?_⟩
  have hx : (WithLp.toLp 2 (β p) : EuclideanSpace ℂ (Fin L)) =
      ∑ l, β p l • EuclideanSpace.single l (1 : ℂ) := by
    ext i
    simp [Pi.single_apply]
  have := congrArg (fun v : EuclideanSpace ℂ (Fin L) => v k) (hT p)
  simp only at this
  rw [← this, hx, map_sum]
  simp only [map_smul, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, U]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

end X4KF

-- ===== KFD =====

noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P41
open QAlgorithms.Papers.Independent.Gap20.P06 (dilationChannel)
open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq
local instance (priority := 2000) instKFD (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

namespace X4KF
open Matrix

variable {d e : ℕ}

/-- `e_i ⊗ η` -/
def wv (eta : EuclideanSpace ℂ (Fin e)) (i : Fin d) : Fin d × Fin e → ℂ :=
  fun p => (if p.1 = i then 1 else 0) * eta p.2

/-- `U (e_i ⊗ η)` -/
def uv (U : Matrix (Fin d × Fin e) (Fin d × Fin e) ℂ) (eta : EuclideanSpace ℂ (Fin e)) (i : Fin d) :
    Fin d × Fin e → ℂ := U *ᵥ wv eta i

lemma prod_eq (v : EuclideanSpace ℂ (Fin d)) (eta : EuclideanSpace ℂ (Fin e)) :
    (fun p : Fin d × Fin e => v p.1 * eta p.2) = ∑ i, v i • wv eta i := by
  ext p
  simp only [wv, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single p.1 (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  simp

lemma act_prod (U : Matrix (Fin d × Fin e) (Fin d × Fin e) ℂ) (v : EuclideanSpace ℂ (Fin d))
    (eta : EuclideanSpace ℂ (Fin e)) (p : Fin d × Fin e) :
    act U (WithLp.toLp 2 fun p => v p.1 * eta p.2) p = ∑ i, v i * uv U eta i p := by
  simp only [act]
  change (U *ᵥ fun p : Fin d × Fin e => v p.1 * eta p.2) p = _
  rw [prod_eq, Matrix.mulVec_sum]
  simp [uv, Matrix.mulVec_smul]

lemma kron_eq (eta : EuclideanSpace ℂ (Fin e)) (i j : Fin d) :
    Matrix.kronecker (Matrix.single i j (1 : ℂ)) (pureDensity eta) =
      vecMulVec (wv eta i) (star (wv eta j)) := by
  ext ⟨a, f⟩ ⟨b, g⟩
  simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.single_apply, pureDensity,
    Matrix.of_apply, vecMulVec_apply, wv, Pi.star_apply, RCLike.star_def]
  by_cases ha : a = i <;> by_cases hb : b = j
  · subst ha; subst hb; simp
  · simp [ha, hb, Ne.symm hb]
  · simp [ha, Ne.symm ha]
  · simp [ha, Ne.symm ha]

lemma chan_entry (U : Matrix.unitaryGroup (Fin d × Fin e) ℂ) (eta : EuclideanSpace ℂ (Fin e))
    (i j a b : Fin d) :
    dilationChannel U eta (Matrix.single i j 1) a b =
      ∑ f, conj (uv U eta j (b, f)) * uv U eta i (a, f) := by
  simp only [dilationChannel, conjSuperop, traceRight, Matrix.of_apply]
  rw [kron_eq, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.star_mulVec]
  refine Finset.sum_congr rfl fun f _ => ?_
  simp only [vecMulVec_apply, Pi.star_apply, RCLike.star_def, uv]
  ring

lemma kron_mulVec (W : Matrix (Fin e) (Fin e) ℂ) (x : Fin d × Fin e → ℂ) (a : Fin d) (f : Fin e) :
    (Matrix.kronecker (1 : Matrix (Fin d) (Fin d) ℂ) W *ᵥ x) (a, f) = ∑ g, W f g * x (a, g) := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single a (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  simp

theorem env_freedom [NeZero d] [NeZero e]
    (U V : Matrix.unitaryGroup (Fin d × Fin e) ℂ)
    (eta zeta : EuclideanSpace ℂ (Fin e))
    (hsame : ∀ X, dilationChannel U eta X = dilationChannel V zeta X) :
    ∃ W : Matrix.unitaryGroup (Fin e) ℂ,
      ∀ v : EuclideanSpace ℂ (Fin d),
        act (V : Matrix (Fin d × Fin e) (Fin d × Fin e) ℂ)
          (WithLp.toLp 2 fun p => v p.1 * zeta p.2) =
        act (Matrix.kronecker (1 : Matrix (Fin d) (Fin d) ℂ)
          (W : Matrix (Fin e) (Fin e) ℂ))
          (act (U : Matrix (Fin d × Fin e) (Fin d × Fin e) ℂ)
            (WithLp.toLp 2 fun p => v p.1 * eta p.2)) := by
  obtain ⟨W, hW⟩ := gram_unitary (L := e) (P := Fin d × Fin d)
    (fun p f => uv V zeta p.1 (p.2, f)) (fun p f => uv U eta p.1 (p.2, f)) (by
      rintro ⟨j, b⟩ ⟨i, a⟩
      simp only
      rw [← chan_entry, ← chan_entry, hsame])
  refine ⟨W, fun v => ?_⟩
  ext ⟨a, f⟩
  rw [act_prod]
  simp only [act]
  rw [kron_mulVec]
  have : ∀ g, (act (U : Matrix (Fin d × Fin e) (Fin d × Fin e) ℂ)
      (WithLp.toLp 2 fun p => v p.1 * eta p.2)).ofLp (a, g) = ∑ i, v i * uv U eta i (a, g) :=
    fun g => act_prod _ v eta (a, g)
  simp only [act] at this
  simp only [this]
  have hW' : ∀ i, uv V zeta i (a, f) = ∑ g, (W : Matrix (Fin e) (Fin e) ℂ) f g * uv U eta i (a, g) :=
    fun i => hW (i, a) f
  simp only [hW', Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun i _ => ?_
  ring

end X4KF

-- ===== KFF =====

noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P41
open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange)
open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)
open QAlgorithms.Papers.Independent.Information100.P50 (complementaryMap)
open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq
local instance (priority := 2000) instKFF (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

namespace X4KF
open Matrix Polynomial

-- entropy swap S(VVᴴ) = S((VᴴV)ᵀ), copied from Solutions/X4/TRC.lean
theorem x4_tr_aeval {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (p : ℝ[X]) :
    (aeval M p).trace = ∑ i ∈ Finset.range (p.natDegree + 1), (p.coeff i : ℂ) * (M ^ i).trace := by
  rw [aeval_eq_sum_range, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.trace_smul]
  simp [Complex.real_smul]

theorem x4_tr_cfc_eq {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (M1 : Matrix ι ι ℂ) (M2 : Matrix κ κ ℂ) (h1 : M1.IsHermitian) (h2 : M2.IsHermitian)
    (h : ∀ k : ℕ, 1 ≤ k → (M1 ^ k).trace = (M2 ^ k).trace) (f : ℝ → ℝ) (hf : f 0 = 0) :
    (cfc f M1).trace = (cfc f M2).trace := by
  classical
  let S : Finset ℝ := Finset.univ.image h1.eigenvalues ∪ Finset.univ.image h2.eigenvalues ∪ {0}
  let p : ℝ[X] := Lagrange.interpolate S id f
  have hp : ∀ x ∈ S, p.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := id) (r := f) (Set.injOn_id _) hx
  have e1 : cfc f M1 = cfc (fun x => p.eval x) M1 := by
    apply cfc_congr
    intro x hx
    rw [h1.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact (hp _ (by simp [S])).symm
  have e2 : cfc f M2 = cfc (fun x => p.eval x) M2 := by
    apply cfc_congr
    intro x hx
    rw [h2.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact (hp _ (by simp [S])).symm
  have h0 : p.coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero, hp 0 (by simp [S]), hf]
  rw [e1, e2, cfc_polynomial p M1, cfc_polynomial p M2, x4_tr_aeval, x4_tr_aeval]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [h0]
  · rw [h i hi]

theorem x4_pow_mul {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (V : Matrix ι κ ℂ) (W : Matrix κ ι ℂ) (k : ℕ) :
    (V * W) ^ (k + 1) = V * (W * V) ^ k * W := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [Matrix.mul_assoc]

theorem x4_tr_pow_swap {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (V : Matrix ι κ ℂ) (W : Matrix κ ι ℂ) (k : ℕ) (hk : 1 ≤ k) :
    ((V * W) ^ k).trace = ((W * V) ^ k).trace := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
  rw [x4_pow_mul, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, ← pow_succ]

/-- tr f(V Vᴴ) = tr f((Vᴴ V)ᵀ) when f 0 = 0. -/
theorem x4_ent_swap {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (V : Matrix ι κ ℂ) :
    QAlgorithms.vnEntropy (V * Vᴴ) = QAlgorithms.vnEntropy ((Vᴴ * V)ᵀ) := by
  unfold QAlgorithms.vnEntropy
  rw [x4_tr_cfc_eq (V * Vᴴ) ((Vᴴ * V)ᵀ) (isHermitian_mul_conjTranspose_self V)
    (isHermitian_conjTranspose_mul_self V).transpose _ _ (by simp)]
  intro k hk
  rw [← Matrix.transpose_pow, Matrix.trace_transpose, x4_tr_pow_swap _ _ k hk]

variable {d m : ℕ}

/-- the coefficient matrix `V_{(r,y),k} = ((1 ⊗ A_k) ψ)(r,y)` -/
def Vm {R : Type} [Fintype R] (A : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (psi : EuclideanSpace ℂ (R × Fin d)) : Matrix (R × Fin d) (Fin m) ℂ :=
  fun p k => ∑ i, A k p.2 i * psi (p.1, i)

lemma idT_eq {R : Type} [Fintype R] (A : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (psi : EuclideanSpace ℂ (R × Fin d)) :
    idTensorSuperop (R := R) (krausApply A) (pureDensity psi) = Vm A psi * (Vm A psi)ᴴ := by
  ext p q
  simp only [idTensorSuperop, krausApply, pureDensity, Matrix.of_apply, Matrix.sum_apply,
    Matrix.mul_apply, Vm, conjTranspose_apply, RCLike.star_def, map_sum, map_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul_sum]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma perm3 {α β γ M : Type*} [Fintype α] [Fintype β] [Fintype γ] [AddCommMonoid M]
    (f : α → β → γ → M) : ∑ r, ∑ a, ∑ b, f r a b = ∑ a, ∑ b, ∑ r, f r a b := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_comm

lemma gram_eq {R : Type} [Fintype R] (A : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (psi : EuclideanSpace ℂ (R × Fin d)) (rho : Matrix (Fin d) (Fin d) ℂ)
    (hK : ∀ j j', ∑ r, psi (r, j) * conj (psi (r, j')) = rho j j') :
    ((Vm A psi)ᴴ * Vm A psi)ᵀ = Matrix.of fun k l => (A k * rho * (A l)ᴴ).trace := by
  ext k l
  simp only [Matrix.transpose_apply, Matrix.mul_apply, conjTranspose_apply, RCLike.star_def,
    Vm, Matrix.of_apply, Matrix.trace, Matrix.diag, Fintype.sum_prod_type, map_sum, map_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp_rw [← hK]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [perm3, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun r _ => ?_
  ring

/-- core: for any purification-type vector, the output entropy is the exchange-matrix entropy. -/
theorem ent_core {R : Type} [Fintype R] (A : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (psi : EuclideanSpace ℂ (R × Fin d)) (rho : Matrix (Fin d) (Fin d) ℂ)
    (hK : ∀ j j', ∑ r, psi (r, j) * conj (psi (r, j')) = rho j j') :
    vnEntropy (idTensorSuperop (R := R) (krausApply A) (pureDensity psi)) =
      vnEntropy (Matrix.of fun k l => (A k * rho * (A l)ᴴ).trace) := by
  rw [idT_eq, x4_ent_swap, gram_eq A psi rho hK]

lemma sqrt_gram {I : Type} [Fintype I] [DecidableEq I] (rho : Matrix I I ℂ) (hrho : rho.PosSemidef)
    (j j' : I) : ∑ r, cfc Real.sqrt rho j r * conj (cfc Real.sqrt rho j' r) = rho j j' := by
  have hS : (cfc Real.sqrt rho)ᴴ = cfc Real.sqrt rho := by
    have : IsSelfAdjoint (cfc Real.sqrt rho) := cfc_predicate _ _
    exact this
  have hsa : IsSelfAdjoint rho := hrho.1
  have hmul : cfc Real.sqrt rho * cfc Real.sqrt rho = rho := by
    rw [← cfc_mul (fun x : ℝ => Real.sqrt x) (fun x : ℝ => Real.sqrt x) rho]
    conv_rhs => rw [← cfc_id' ℝ rho]
    apply cfc_congr
    intro x hx
    have : 0 ≤ x := by
      have := hrho.1.spectrum_real_eq_range_eigenvalues ▸ hx
      obtain ⟨i, rfl⟩ := this
      exact hrho.eigenvalues_nonneg i
    exact Real.mul_self_sqrt this
  have := congrFun (congrFun hmul j) j'
  rw [Matrix.mul_apply] at this
  rw [← this]
  refine Finset.sum_congr rfl fun r _ => ?_
  congr 1
  have h2 := congrFun (congrFun hS j') r
  rw [conjTranspose_apply, RCLike.star_def] at h2
  rw [← h2]
  simp

theorem ent_exchange [NeZero d] (Phi : Superop (Fin d) (Fin d)) (A : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ X, Phi X = krausApply A X)
    (rho : Matrix (Fin d) (Fin d) ℂ) (hrho : rho.PosSemidef) :
    entropyExchange Phi rho = vnEntropy (Matrix.of fun k l => (A k * rho * (A l)ᴴ).trace) := by
  have hPhi : Phi = krausApply A := funext hA
  subst hPhi
  unfold entropyExchange
  simp only
  apply ent_core
  intro j j'
  simp only [canonicalPurification]
  set e := Fintype.equivFin (Fin d)
  have hpsd : (show Matrix (Fin (Fintype.card (Fin d))) (Fin (Fintype.card (Fin d))) ℂ from
      fun i j => rho (e.symm i) (e.symm j)).PosSemidef := hrho.submatrix e.symm
  have := @sqrt_gram (Fin (Fintype.card (Fin d))) _ (instDecidableEqFin _) _ hpsd (e j) (e j')
  simp only [Equiv.symm_apply_apply] at this
  rw [← this]
  exact Fintype.sum_equiv e _ _ (fun r => rfl)

end X4KF

-- ===== KFG =====

noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P41
open QAlgorithms.Papers.Independent.Dependency50.P40 (IsPurification)
open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange)
open QAlgorithms.Papers.Independent.Information100.P50 (complementaryMap)
open QAlgorithms.Papers.Independent.Gap20.P06 (dilationChannel environmentOutput)
open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq
attribute [local instance 2000] instKFF

namespace X4KF
open Matrix

variable {d m : ℕ}

lemma perm3b {α β γ M : Type*} [Fintype α] [Fintype β] [Fintype γ] [AddCommMonoid M]
    (f : α → β → γ → M) : ∑ a, ∑ b, ∑ y, f a b y = ∑ y, ∑ b, ∑ a, f a b y := by
  rw [perm3 f, Finset.sum_comm]

lemma cm_eq (A : Fin m → Matrix (Fin d) (Fin d) ℂ) (rho : Matrix (Fin d) (Fin d) ℂ) (k l : Fin m) :
    complementaryMap A rho k l = (A k * rho * (A l)ᴴ).trace := by
  change (∑ a, ∑ b, (∑ y, A k y a * conj (A l y b)) * rho a b) = _
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, conjTranspose_apply, RCLike.star_def,
    Finset.sum_mul]
  rw [perm3b]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun a _ => ?_
  ring

lemma W_density (A : Fin m → Matrix (Fin d) (Fin d) ℂ) (hA : IsKrausFamily A)
    (rho : Matrix (Fin d) (Fin d) ℂ) (hrho : IsDensityMatrix rho) :
    IsDensityMatrix (Matrix.of fun k l => (A k * rho * (A l)ᴴ).trace) := by
  refine ⟨?_, ?_⟩
  · let psi : EuclideanSpace ℂ (Fin d × Fin d) := WithLp.toLp 2 fun z => cfc Real.sqrt rho z.2 z.1
    have hK : ∀ j j', ∑ r, psi (r, j) * conj (psi (r, j')) = rho j j' :=
      fun j j' => sqrt_gram rho hrho.1 j j'
    rw [← gram_eq A psi rho hK]
    exact (Matrix.posSemidef_conjTranspose_mul_self _).transpose
  · simp only [Matrix.trace, Matrix.diag, Matrix.of_apply]
    have : ∑ k, ∑ i, (A k * rho * (A k)ᴴ) i i = ((∑ k, (A k)ᴴ * A k) * rho).trace := by
      rw [Matrix.sum_mul, Matrix.trace_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      change (A k * rho * (A k)ᴴ).trace = _
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
    rw [this, hA, Matrix.one_mul, hrho.2]

theorem exchange (Phi : Superop (Fin d) (Fin d)) [NeZero d] (A : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (hA : OperatorSum Phi A)
    (rho : Matrix (Fin d) (Fin d) ℂ) (hrho : IsDensityMatrix rho) :
    (∀ k l, complementaryMap A rho k l = (A k * rho * (A l)ᴴ).trace) ∧
    IsDensityMatrix (complementaryMap A rho) ∧
    entropyExchange Phi rho = vnEntropy (complementaryMap A rho) := by
  have hW : complementaryMap A rho = Matrix.of fun k l => (A k * rho * (A l)ᴴ).trace := by
    ext k l; exact cm_eq A rho k l
  refine ⟨cm_eq A rho, ?_, ?_⟩
  · rw [hW]; exact W_density A hA.1 rho hrho
  · rw [hW]; exact ent_exchange Phi A hA.2 rho hrho.1

theorem intrinsic {a b : ℕ} [NeZero d]
    (Phi : Superop (Fin d) (Fin d)) (hPhi : IsChannel Phi)
    (rho : Matrix (Fin d) (Fin d) ℂ) (hrho : IsDensityMatrix rho)
    (psi : EuclideanSpace ℂ (Fin a × Fin d)) (hpsi : IsPurification rho psi)
    (phi : EuclideanSpace ℂ (Fin b × Fin d)) (hphi : IsPurification rho phi) :
    vnEntropy (idTensorSuperop Phi (pureDensity psi)) = entropyExchange Phi rho ∧
    vnEntropy (idTensorSuperop Phi (pureDensity phi)) = entropyExchange Phi rho := by
  obtain ⟨n, E, -, hE⟩ := hPhi
  have hP : Phi = krausApply E := funext hE
  rw [ent_exchange Phi E hE rho hrho.1, hP]
  refine ⟨ent_core E psi rho fun j j' => ?_, ent_core E phi rho fun j j' => ?_⟩
  · have := congrFun (congrFun hpsi.2 j) j'
    simpa [traceLeft, pureDensity] using this
  · have := congrFun (congrFun hphi.2 j) j'
    simpa [traceLeft, pureDensity] using this

variable {e : ℕ}

/-- `I ⊗ |η⟩` -/
def Keta (eta : EuclideanSpace ℂ (Fin e)) : Matrix (Fin d × Fin e) (Fin d) ℂ :=
  Matrix.of fun p j => if p.1 = j then eta p.2 else 0

lemma kron_K (eta : EuclideanSpace ℂ (Fin e)) (X : Matrix (Fin d) (Fin d) ℂ) :
    Matrix.kronecker X (pureDensity eta) =
      (Keta (d := d) eta * X * (Keta (d := d) eta)ᴴ : Matrix (Fin d × Fin e) (Fin d × Fin e) ℂ) := by
  ext ⟨j, g⟩ ⟨j', g'⟩
  simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, pureDensity, Matrix.of_apply,
    Matrix.mul_apply, Keta, conjTranspose_apply, RCLike.star_def]
  rw [Finset.sum_eq_single j' (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  rw [Finset.sum_eq_single j (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  simp
  ring

/-- Kraus operators of the dilation: `A_f = (I ⊗ ⟨f|) U (I ⊗ |η⟩)` -/
def Adil (U : Matrix (Fin d × Fin e) (Fin d × Fin e) ℂ) (eta : EuclideanSpace ℂ (Fin e)) (f : Fin e) :
    Matrix (Fin d) (Fin d) ℂ :=
  fun a j => (U * Keta (d := d) eta : Matrix (Fin d × Fin e) (Fin d) ℂ) (a, f) j

lemma reassoc (U : Matrix (Fin d × Fin e) (Fin d × Fin e) ℂ) (eta : EuclideanSpace ℂ (Fin e))
    (X : Matrix (Fin d) (Fin d) ℂ) :
    U * (Keta (d := d) eta * X * (Keta (d := d) eta)ᴴ : Matrix (Fin d × Fin e) (Fin d × Fin e) ℂ) * Uᴴ =
      ((U * Keta (d := d) eta : Matrix (Fin d × Fin e) (Fin d) ℂ) * X *
        (U * Keta (d := d) eta : Matrix (Fin d × Fin e) (Fin d) ℂ)ᴴ :
          Matrix (Fin d × Fin e) (Fin d × Fin e) ℂ) := by
  rw [Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

lemma dil_kraus (U : Matrix.unitaryGroup (Fin d × Fin e) ℂ) (eta : EuclideanSpace ℂ (Fin e))
    (X : Matrix (Fin d) (Fin d) ℂ) :
    dilationChannel U eta X = krausApply (Adil (U : Matrix _ _ ℂ) eta) X := by
  simp only [dilationChannel, conjSuperop]
  rw [kron_K, reassoc]
  ext a b
  simp only [traceRight, krausApply, Matrix.of_apply, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun f _ => ?_
  simp only [Matrix.mul_apply, conjTranspose_apply, Adil]

lemma env_eq (U : Matrix.unitaryGroup (Fin d × Fin e) ℂ) (eta : EuclideanSpace ℂ (Fin e))
    (rho : Matrix (Fin d) (Fin d) ℂ) :
    environmentOutput U eta rho =
      Matrix.of fun k l => (Adil (U : Matrix _ _ ℂ) eta k * rho * (Adil (U : Matrix _ _ ℂ) eta l)ᴴ).trace := by
  simp only [environmentOutput, conjSuperop]
  rw [kron_K, reassoc]
  ext k l
  simp only [traceLeft, Matrix.of_apply, Matrix.trace, Matrix.diag]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Matrix.mul_apply, conjTranspose_apply, Adil]

theorem environment [NeZero d] [NeZero e]
    (U : Matrix.unitaryGroup (Fin d × Fin e) ℂ) (eta : EuclideanSpace ℂ (Fin e))
    (rho : Matrix (Fin d) (Fin d) ℂ) (hrho : IsDensityMatrix rho) :
    entropyExchange (dilationChannel U eta) rho = vnEntropy (environmentOutput U eta rho) := by
  have h1 := ent_exchange (d := d) (m := e) (dilationChannel U eta)
    (Adil (d := d) (e := e) (U : Matrix (Fin d × Fin e) (Fin d × Fin e) ℂ) eta)
    (fun X => dil_kraus U eta X) rho hrho.1
  rw [h1, env_eq]

end X4KF

-- ===== DP =====

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P41

open QAlgorithms

open QAlgorithms.Entanglement (IsCompletelyPositive)

open QAlgorithms.Papers.Independent.Dependency50.P40 (IsPurification purificationFidelity)

open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange)

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)

open QAlgorithms.Papers.Independent.Information100.P34 (choi dephasing)

open QAlgorithms.Papers.Independent.Dependency50.P38 (vectorizeInputFirst)

open QAlgorithms.Papers.Independent.Gap20.P06 (dilationChannel environmentOutput dilatedVector)

open QAlgorithms.Papers.Independent.Information100.P50 (complementaryMap)

open QAlgorithms.Papers.Independent.Renew46.P43 (IsCountablePOVM classicalKLTerm countableEntropy)

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

-- The accepted generic dilation functions fix classical equality on each factor.
-- Match that instance for Fin before forming their product unitary groups.

local instance (priority := 2000) instDP (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _


namespace X4DP
open Matrix X4KF
open scoped InnerProductSpace

variable {d e : ℕ}

lemma gram_unitary2 {P ι : Type*} [Fintype P] [Fintype ι] [DecidableEq ι] (α β : P → ι → ℂ)
    (h : ∀ p q, ∑ l, conj (β p l) * β q l = ∑ l, conj (α p l) * α q l) :
    ∃ U : Matrix.unitaryGroup ι ℂ, ∀ p k,
      α p k = ∑ l, (U : Matrix ι ι ℂ) k l * β p l := by
  have hin : ∀ x y : ι → ℂ, ⟪(WithLp.toLp 2 x : EuclideanSpace ℂ ι), WithLp.toLp 2 y⟫_ℂ =
      ∑ l, conj (x l) * y l := by
    intro x y
    simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]
  obtain ⟨T, hT⟩ := gram_iso (V := EuclideanSpace ℂ ι) (fun p => WithLp.toLp 2 (α p))
    (fun p => WithLp.toLp 2 (β p)) (by
      intro p q
      rw [hin, hin, h])
  let U : Matrix ι ι ℂ := fun k l => T (EuclideanSpace.single l 1) k
  have hcol : ∀ l l', ∑ k, conj (U k l) * U k l' = if l = l' then 1 else 0 := by
    intro l l'
    have := T.inner_map_map (EuclideanSpace.single l (1 : ℂ)) (EuclideanSpace.single l' 1)
    have e1 := hin (T (EuclideanSpace.single l (1 : ℂ))).ofLp (T (EuclideanSpace.single l' (1 : ℂ))).ofLp
    simp only [WithLp.toLp_ofLp] at e1
    rw [e1] at this
    simp only [U]
    rw [this, EuclideanSpace.inner_single_left]
    simp [PiLp.single_apply]
  have hU : star U * U = 1 := by
    ext l l'
    simp only [Matrix.mul_apply, Matrix.star_apply, RCLike.star_def, Matrix.one_apply]
    exact hcol l l'
  refine ⟨⟨U, Matrix.mem_unitaryGroup_iff'.mpr hU⟩, fun p k => ?_⟩
  have hx : (WithLp.toLp 2 (β p) : EuclideanSpace ℂ ι) =
      ∑ l, β p l • EuclideanSpace.single l (1 : ℂ) := by
    ext i
    simp [Pi.single_apply]
  have := congrArg (fun v : EuclideanSpace ℂ ι => v k) (hT p)
  simp only at this
  rw [← this, hx, map_sum]
  simp only [map_smul, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, U]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

lemma adil_uv (U : Matrix (Fin d × Fin e) (Fin d × Fin e) ℂ) (eta : EuclideanSpace ℂ (Fin e))
    (f : Fin e) (a i : Fin d) : Adil U eta f a i = uv U eta i (a, f) := by
  simp only [Adil, uv, wv, Keta, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.of_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  split_ifs with h1 h2 h2 <;> simp_all

lemma conj_entry' (A X : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    (A * X * Aᴴ) i j = ∑ a, ∑ b, X a b * (A i a * conj (A j b)) := by
  simp only [Matrix.mul_apply, conjTranspose_apply, RCLike.star_def, Finset.sum_mul]
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring

lemma dil_entry (U : Matrix.unitaryGroup (Fin d × Fin e) ℂ) (eta : EuclideanSpace ℂ (Fin e))
    (X : Matrix (Fin d) (Fin d) ℂ) (a b : Fin d) :
    dilationChannel U eta X a b =
      ∑ i, ∑ j, X i j * ∑ f, uv (U : Matrix _ _ ℂ) eta i (a, f) * conj (uv (U : Matrix _ _ ℂ) eta j (b, f)) := by
  rw [dil_kraus]
  simp only [krausApply, Matrix.sum_apply, conj_entry', adil_uv, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

lemma phi_entry {Phi : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ}
    (X : Matrix (Fin d) (Fin d) ℂ) (a b : Fin d) :
    Phi X a b = ∑ i, ∑ j, X i j * choi Phi (i, a) (j, b) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum, Matrix.sum_apply, choi]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show Matrix.single i j (X i j) = X i j • Matrix.single i j (1:ℂ) by simp, map_smul]
  rfl

lemma tr_choi {Phi : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ}
    (hTP : ∀ X, (Phi X).trace = X.trace) (r r' : Fin d) :
    ∑ q, choi Phi (r, q) (r', q) = if r = r' then 1 else 0 := by
  have := hTP (Matrix.single r r' 1)
  simp only [Matrix.trace, Matrix.diag] at this
  simp only [choi, this, Matrix.single_apply]
  rw [Finset.sum_eq_single r (by intro b _ hb; simp [Ne.symm hb]) (by simp)]
  simp [eq_comm]

lemma sq_d [NeZero d] : ((Real.sqrt d : ℂ)) * (Real.sqrt d : ℂ) = d := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]; simp

lemma sqd_ne [NeZero d] : (Real.sqrt d : ℂ) ≠ 0 := by
  have : (0:ℝ) < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d))
  exact_mod_cast this.ne'

lemma dcv [NeZero d] (U : Matrix.unitaryGroup (Fin d × Fin e) ℂ) (eta : EuclideanSpace ℂ (Fin e))
    (r q : Fin d) (f : Fin e) :
    dilationChoiVector U eta ((r, q), f) = (Real.sqrt d : ℂ)⁻¹ * uv (U : Matrix _ _ ℂ) eta r (q, f) := by
  simp only [dilationChoiVector, dilatedVector, act, PiLp.toLp_apply, uv, wv, Matrix.mulVec,
    dotProduct, Fintype.sum_prod_type, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply,
    finiteMaxEntangled, Fintype.card_fin, Finset.mul_sum]
  rw [Finset.sum_eq_single r (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  refine Finset.sum_congr rfl fun q' _ => Finset.sum_congr rfl fun f' _ => ?_
  by_cases h : r = q'
  · subst h; simp; ring
  · simp [h, Ne.symm h]

lemma state_of {ι : Type*} [Fintype ι] (v : EuclideanSpace ℂ ι) (h : ∑ p, conj (v p) * v p = 1) :
    IsState v := by
  have h2 : ‖v‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    have : ((∑ p, ‖v p‖ ^ 2 : ℝ) : ℂ) = 1 := by
      rw [← h]; push_cast; exact Finset.sum_congr rfl fun p _ => (RCLike.conj_mul _).symm
    exact_mod_cast this
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h2

lemma state_sum {ι : Type*} [Fintype ι] (v : EuclideanSpace ℂ ι) (h : IsState v) :
    ∑ p, conj (v p) * v p = 1 := by
  have h2 : ‖v‖ ^ 2 = 1 := by rw [show ‖v‖ = 1 from h]; norm_num
  rw [EuclideanSpace.norm_sq_eq] at h2
  have : ((∑ p, ‖v p‖ ^ 2 : ℝ) : ℂ) = 1 := by exact_mod_cast h2
  rw [← this]; push_cast; exact Finset.sum_congr rfl fun p _ => RCLike.conj_mul _

end X4DP

end QAlgorithms.Papers.Independent.Support50.P41

end

-- ===== FanoLib =====

/-! Generic: Schur concavity of von Neumann entropy and the (quantum) Fano bound. -/

noncomputable section

namespace X4FN
open Matrix Real QAlgorithms
open scoped Matrix ComplexConjugate ComplexOrder

/-- classical Fano / grouping bound. -/
lemma fano_classical {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℝ) (h0 : ∀ i, 0 ≤ p i)
    (h1 : ∑ i, p i = 1) (i0 : ι) (hN : 2 ≤ Fintype.card ι) :
    ∑ i, negMulLog (p i) ≤
      binEntropy (p i0) + (1 - p i0) * Real.log ((Fintype.card ι : ℝ) - 1) := by
  set t := Finset.univ.erase i0
  have hct : (t.card : ℝ) = (Fintype.card ι : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    have : 1 ≤ Fintype.card ι := by omega
    push_cast [this]; ring
  have hpos : (0:ℝ) < t.card := by
    rw [hct]; have : (2:ℝ) ≤ Fintype.card ι := by exact_mod_cast hN
    linarith
  have hs : ∑ i ∈ t, p i = 1 - p i0 := by
    rw [← h1, ← Finset.add_sum_erase _ _ (Finset.mem_univ i0)]; ring
  have hsplit : ∑ i, negMulLog (p i) = negMulLog (p i0) + ∑ i ∈ t, negMulLog (p i) :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ i0)).symm
  -- Jensen with uniform weights on t
  have hJ := concaveOn_negMulLog.le_map_sum (t := t) (w := fun _ => (t.card : ℝ)⁻¹) (p := p)
    (fun _ _ => by positivity) (by simp [Finset.sum_const, hpos.ne']) (fun i _ => h0 i)
  simp only [smul_eq_mul, ← Finset.mul_sum, hs] at hJ
  have hJ' : ∑ i ∈ t, negMulLog (p i) ≤ t.card * negMulLog ((t.card : ℝ)⁻¹ * (1 - p i0)) := by
    have := mul_le_mul_of_nonneg_left hJ hpos.le
    rwa [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul] at this
  have hval : (t.card : ℝ) * negMulLog ((t.card : ℝ)⁻¹ * (1 - p i0)) =
      negMulLog (1 - p i0) + (1 - p i0) * Real.log (t.card) := by
    rcases eq_or_ne (1 - p i0) 0 with hz | hz
    · rw [hz]; simp
    · simp only [negMulLog]
      rw [Real.log_mul (inv_ne_zero hpos.ne') hz, Real.log_inv]
      field_simp
      ring
  rw [hsplit, binEntropy_eq_negMulLog_add_negMulLog_one_sub, ← hct]
  linarith

/-- trace of a cfc over a general finite index. -/
lemma cfc_trace {ι : Type*} [Fintype ι] [DecidableEq ι] {Y : Matrix ι ι ℂ} (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma vn_eig {ι : Type*} [Fintype ι] [DecidableEq ι] {Y : Matrix ι ι ℂ} (hY : Y.IsHermitian) :
    vnEntropy Y = (∑ i, negMulLog (hY.eigenvalues i)) / Real.log 2 := by
  unfold vnEntropy
  rw [cfc_trace hY]
  simp only [Complex.re_sum, Complex.ofReal_re, negMulLog, Real.logb, Finset.sum_div,
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma ds_sums {ι : Type*} [Fintype ι] [DecidableEq ι] (W : Matrix ι ι ℂ)
    (hW : W ∈ Matrix.unitaryGroup ι ℂ) :
    (∀ i, ∑ k, Complex.normSq (W k i) = 1) ∧ (∀ k, ∑ i, Complex.normSq (W k i) = 1) := by
  constructor
  · intro i
    have := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.1 hW) i) i
    simp only [Matrix.mul_apply, star_apply, RCLike.star_def, Matrix.one_apply_eq] at this
    have h2 : ((∑ k, Complex.normSq (W k i) : ℝ) : ℂ) = 1 := by
      rw [← this]; push_cast; simp only [Complex.normSq_eq_conj_mul_self]
    exact_mod_cast h2
  · intro k
    have := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.1 hW) k) k
    simp only [Matrix.mul_apply, star_apply, RCLike.star_def, Matrix.one_apply_eq] at this
    have h2 : ((∑ i, Complex.normSq (W k i) : ℝ) : ℂ) = 1 := by
      rw [← this]; push_cast; simp only [Complex.normSq_eq_conj_mul_self]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    exact_mod_cast h2

lemma jensen_ds {ι : Type*} [Fintype ι] (lam : ι → ℝ) (hl0 : ∀ k, 0 ≤ lam k) (w : ι → ι → ℝ)
    (hw0 : ∀ i k, 0 ≤ w i k) (hcol : ∀ i, ∑ k, w i k = 1) (hrow : ∀ k, ∑ i, w i k = 1) :
    ∑ k, negMulLog (lam k) ≤ ∑ i, negMulLog (∑ k, w i k * lam k) := by
  calc ∑ k, negMulLog (lam k) = ∑ k, ∑ i, w i k * negMulLog (lam k) := by
        simp only [← Finset.sum_mul, hrow, one_mul]
    _ = ∑ i, ∑ k, w i k * negMulLog (lam k) := Finset.sum_comm
    _ ≤ ∑ i, negMulLog (∑ k, w i k * lam k) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have := concaveOn_negMulLog.le_map_sum (t := Finset.univ) (w := w i) (p := lam)
          (fun k _ => hw0 i k) (hcol i) (fun k _ => hl0 k)
        simpa only [smul_eq_mul] using this

lemma diag_conj {ι : Type*} [Fintype ι] [DecidableEq ι] (U V : Matrix ι ι ℂ) (lam : ι → ℝ) (i : ι) :
    (Uᴴ * (V * diagonal (RCLike.ofReal ∘ lam : ι → ℂ) * star V) * U : Matrix ι ι ℂ) i i =
      ∑ k, ((Complex.normSq ((star V * U) k i) * lam k : ℝ) : ℂ) := by
  have hm : Uᴴ * (V * diagonal (RCLike.ofReal ∘ lam : ι → ℂ) * star V) * U =
      (star V * U)ᴴ * diagonal (RCLike.ofReal ∘ lam : ι → ℂ) * (star V * U) := by
    simp only [conjTranspose_mul, Matrix.mul_assoc, Matrix.star_eq_conjTranspose,
      conjTranspose_conjTranspose]
  rw [hm, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_diagonal, conjTranspose_apply, RCLike.star_def]
  simp only [Function.comp_apply, Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]
  exact mul_right_comm (G := ℂ) _ _ _

/-- Schur concavity: the entropy of a basis diagonal dominates the von Neumann entropy. -/
lemma schur {ι : Type*} [Fintype ι] [DecidableEq ι] {σ : Matrix ι ι ℂ} (hσ : σ.PosSemidef)
    (U : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    (∀ i, 0 ≤ ((Uᴴ * σ * U) i i).re) ∧ ∑ i, ((Uᴴ * σ * U) i i).re = (σ.trace).re ∧
    vnEntropy σ ≤ (∑ i, negMulLog ((Uᴴ * σ * U) i i).re) / Real.log 2 := by
  obtain ⟨V, lam, hl0, htr, hvn, hV⟩ : ∃ (V : Matrix.unitaryGroup ι ℂ) (lam : ι → ℝ),
      (∀ k, 0 ≤ lam k) ∧ σ.trace = ∑ k, (lam k : ℂ) ∧
      vnEntropy σ = (∑ k, negMulLog (lam k)) / Real.log 2 ∧
      σ = (V : Matrix ι ι ℂ) * diagonal (RCLike.ofReal ∘ lam : ι → ℂ) * star (V : Matrix ι ι ℂ) :=
    ⟨hσ.1.eigenvectorUnitary, hσ.1.eigenvalues, hσ.eigenvalues_nonneg,
      by rw [hσ.1.trace_eq_sum_eigenvalues]; rfl, vn_eig hσ.1, by
      conv_lhs => rw [hσ.1.spectral_theorem]
      rw [Unitary.conjStarAlgAut_apply]⟩
  have hW : star (V : Matrix ι ι ℂ) * U ∈ Matrix.unitaryGroup ι ℂ :=
    Submonoid.mul_mem _ (Unitary.star_mem V.2) hU
  obtain ⟨hcol, hrow⟩ := ds_sums _ hW
  have hdiag : ∀ i, ((Uᴴ * σ * U) i i).re =
      ∑ k, Complex.normSq ((star (V : Matrix ι ι ℂ) * U) k i) * lam k := by
    intro i
    rw [hV, diag_conj, Complex.re_sum]; simp
  refine ⟨fun i => by
    rw [hdiag]; exact Finset.sum_nonneg fun k _ => mul_nonneg (Complex.normSq_nonneg _) (hl0 k),
    ?_, ?_⟩
  · simp only [hdiag]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, hrow, one_mul]
    rw [htr]; simp
  · rw [hvn]
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    refine div_le_div_of_nonneg_right ?_ hl2.le
    simp only [hdiag]
    exact jensen_ds _ hl0 _ (fun _ _ => Complex.normSq_nonneg _) hcol hrow

/-- quantum Fano bound for a density matrix and unit vector. -/
theorem fano {ι : Type*} [Fintype ι] [DecidableEq ι] {σ : Matrix ι ι ℂ} (hσ : σ.PosSemidef)
    (htr : σ.trace = 1) (ψ : ι → ℂ) (hψ : ∑ i, conj (ψ i) * ψ i = 1)
    (hN : 2 ≤ Fintype.card ι) :
    ((∑ a, ∑ b, conj (ψ a) * σ a b * ψ b).re ≤ 1) ∧
    vnEntropy σ ≤ binEntropy2 (∑ a, ∑ b, conj (ψ a) * σ a b * ψ b).re +
      (1 - (∑ a, ∑ b, conj (ψ a) * σ a b * ψ b).re) * Real.logb 2 ((Fintype.card ι : ℝ) - 1) := by
  have hne : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨i0⟩ := hne
  obtain ⟨U, hU⟩ := QAlgorithms.Papers.Independent.Support50.P41.X4DP.gram_unitary2 (P := Unit) (fun _ => ψ) (fun _ => Pi.single i0 1) (by
    intro p q
    simp only [hψ]
    rw [Finset.sum_eq_single i0 (fun b _ hb => by simp [hb]) (by simp)]
    simp)
  have hcol : ∀ k, ψ k = (U : Matrix ι ι ℂ) k i0 := by
    intro k; rw [hU () k]
    rw [Finset.sum_eq_single i0 (fun b _ hb => by simp [hb]) (by simp)]
    simp
  obtain ⟨h0, h1, h2⟩ := schur hσ (U : Matrix ι ι ℂ) U.2
  set p := fun i => (((U : Matrix ι ι ℂ)ᴴ * σ * U) i i).re
  have hp0 : p i0 = (∑ a, ∑ b, conj (ψ a) * σ a b * ψ b).re := by
    simp only [p, Matrix.mul_apply, conjTranspose_apply, RCLike.star_def, hcol, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [htr, Complex.one_re] at h1
  have hF := fano_classical p h0 h1 i0 hN
  rw [← hp0]
  refine ⟨h1 ▸ Finset.single_le_sum (fun i _ => h0 i) (Finset.mem_univ i0), h2.trans ?_⟩
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [div_le_iff₀ hl2]
  simp only [binEntropy2, Real.logb]
  calc _ ≤ _ := hF
    _ = _ := by field_simp

lemma vn_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] {σ : Matrix ι ι ℂ} (hσ : σ.PosSemidef)
    (htr : σ.trace = 1) : 0 ≤ vnEntropy σ := by
  rw [vn_eig hσ.1]
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine div_nonneg (Finset.sum_nonneg fun k _ => ?_) hl2.le
  have h0 := hσ.eigenvalues_nonneg
  have hs : ∑ k, hσ.1.eigenvalues k = 1 := by
    have := congrArg Complex.re (hσ.1.trace_eq_sum_eigenvalues.symm.trans htr)
    simpa [Complex.re_sum] using this
  exact Real.negMulLog_nonneg (h0 k) (hs ▸ Finset.single_le_sum (fun i _ => h0 i) (Finset.mem_univ k))

lemma fano_one {ι : Type*} [Fintype ι] [DecidableEq ι] {σ : Matrix ι ι ℂ} (hσ : σ.PosSemidef)
    (htr : σ.trace = 1) (ψ : ι → ℂ) (hψ : ∑ i, conj (ψ i) * ψ i = 1)
    (h1 : Fintype.card ι = 1) :
    (∑ a, ∑ b, conj (ψ a) * σ a b * ψ b).re = 1 ∧ vnEntropy σ = 0 := by
  obtain ⟨x, hx⟩ := Fintype.card_eq_one_iff.1 h1
  have hs : ∀ f : ι → ℂ, ∑ i, f i = f x := fun f =>
    Fintype.sum_eq_single x (fun y hy => absurd (hx y) hy)
  rw [hs] at hψ
  have hσx : σ x x = 1 := by rw [← htr, Matrix.trace, hs]; rfl
  refine ⟨by rw [hs, hs, hσx, mul_one, hψ, Complex.one_re], le_antisymm ?_ (vn_nonneg hσ htr)⟩
  obtain ⟨-, -, h2⟩ := schur hσ 1 (one_mem _)
  refine h2.trans (le_of_eq ?_)
  rw [Fintype.sum_eq_single x (fun y hy => absurd (hx y) hy)]
  simp [hσx]

end X4FN

-- ===== P41Lib =====

noncomputable section

namespace X4P41L

open QAlgorithms
open QAlgorithms.Papers.Independent.Support50.P41
open QAlgorithms.Papers.Independent.Dependency50.P40 (IsPurification purificationFidelity
  complexQuadraticForm)
open QAlgorithms.Papers.Independent.Information100.P34 (choi dephasing)
open scoped Matrix ComplexConjugate
open Matrix

attribute [local instance] Classical.propDecidable Classical.decEq
local instance (priority := 2000) (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

variable {a d m : ℕ}

/-- the Kraus-branch vectors -/
def phi (A : Fin m → Matrix (Fin d) (Fin d) ℂ) (psi : EuclideanSpace ℂ (Fin a × Fin d))
    (k : Fin m) : EuclideanSpace ℂ (Fin a × Fin d) :=
  WithLp.toLp 2 fun p => ∑ i, A k p.2 i * psi (p.1, i)

lemma idTensor_kraus (A : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (psi : EuclideanSpace ℂ (Fin a × Fin d)) :
    idTensorSuperop (krausApply A) (pureDensity psi) = ∑ k, pureDensity (phi A psi k) := by
  ext p q
  simp only [idTensorSuperop, krausApply, Matrix.of_apply, Matrix.sum_apply, Matrix.mul_apply,
    pureDensity, conjTranspose_apply, phi, PiLp.toLp_apply, map_sum, map_mul, RCLike.star_def,
    Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma cqf_sum {ι K : Type*} [Fintype ι] [Fintype K] (v : EuclideanSpace ℂ ι)
    (M : K → Matrix ι ι ℂ) :
    complexQuadraticForm v (∑ k, M k) = ∑ k, complexQuadraticForm v (M k) := by
  simp only [complexQuadraticForm, Matrix.sum_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_congr rfl (fun x _ => Finset.sum_comm), Finset.sum_comm]

lemma cqf_pure {ι : Type*} [Fintype ι] (v w : EuclideanSpace ℂ ι) :
    complexQuadraticForm v (pureDensity w) = (Complex.normSq (∑ x, conj (v x) * w x) : ℂ) := by
  rw [Complex.normSq_eq_conj_mul_self]
  simp only [complexQuadraticForm, pureDensity, Matrix.of_apply, map_sum, map_mul,
    Complex.conj_conj, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

lemma overlap_trace (A : Matrix (Fin d) (Fin d) ℂ) (psi : EuclideanSpace ℂ (Fin a × Fin d))
    (k : Fin m) (B : Fin m → Matrix (Fin d) (Fin d) ℂ) (hB : B k = A) :
    ∑ x, conj (psi x) * phi B psi k x = (traceLeft (pureDensity psi) * A).trace := by
  simp only [phi, PiLp.toLp_apply, hB, Matrix.trace, Matrix.diag, Matrix.mul_apply, traceLeft,
    pureDensity, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun r _ => ?_
  ring

theorem kraus_fid (A : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (psi : EuclideanSpace ℂ (Fin a × Fin d)) :
    purificationFidelity psi (krausApply A) =
      ∑ k, Complex.normSq ((traceLeft (pureDensity psi) * A k).trace) := by
  unfold purificationFidelity
  rw [idTensor_kraus, cqf_sum]
  simp_rw [cqf_pure]
  rw [← Complex.ofReal_sum, Complex.ofReal_re]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [overlap_trace (A k) psi k A rfl]

lemma choi_rel {d : ℕ} (Phi : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (v : EuclideanSpace ℂ (Fin d)) :
    Phi (pureDensity v) = relativeOperator (indexState v) (choi Phi) := by
  have hv : pureDensity v = ∑ i, ∑ l, (v i * conj (v l)) • Matrix.single i l (1 : ℂ) := by
    ext x y
    simp only [pureDensity, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.single_apply, smul_eq_mul]
    rw [Finset.sum_eq_single x]
    · rw [Finset.sum_eq_single y]
      · simp
      · intro b _ hb; simp [Ne.symm hb, hb]
      · simp
    · intro b _ hb
      refine Finset.sum_eq_zero fun c _ => ?_
      simp [Ne.symm hb, hb]
    · simp
  ext j k
  rw [hv]
  simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    relativeOperator, indexState, PiLp.toLp_apply, Complex.conj_conj, choi]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  ring

end X4P41L

-- ===== RFano =====

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P41

open QAlgorithms

open QAlgorithms.Entanglement (IsCompletelyPositive)

open QAlgorithms.Papers.Independent.Dependency50.P40 (IsPurification purificationFidelity)

open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange)

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)

open QAlgorithms.Papers.Independent.Information100.P34 (choi dephasing)

open QAlgorithms.Papers.Independent.Dependency50.P38 (vectorizeInputFirst)

open QAlgorithms.Papers.Independent.Gap20.P06 (dilationChannel environmentOutput dilatedVector)

open QAlgorithms.Papers.Independent.Information100.P50 (complementaryMap)

open QAlgorithms.Papers.Independent.Renew46.P43 (IsCountablePOVM classicalKLTerm countableEntropy)

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

-- The accepted generic dilation functions fix classical equality on each factor.
-- Match that instance for Fin before forming their product unitary groups.

local instance (priority := 2000) instRF (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _


namespace X4RF
open Matrix X4KF

lemma core {d m b a : ℕ} [NeZero d]
    (Phi : Superop (Fin d) (Fin d))
    (A : Fin m → Matrix (Fin d) (Fin d) ℂ) (hKF : IsKrausFamily A) (hA : ∀ X, Phi X = krausApply A X)
    (rho : Matrix (Fin d) (Fin d) ℂ) (hrho : IsDensityMatrix rho)
    (psi : EuclideanSpace ℂ (Fin a × Fin d)) (hpsi : IsPurification rho psi)
    (ψ1 : EuclideanSpace ℂ (Fin b × Fin d))
    (hK0 : ∀ j j', ∑ r, ψ1 (r, j) * conj (ψ1 (r, j')) = rho j j') :
    let σ := idTensorSuperop (krausApply A) (pureDensity ψ1)
    σ.PosSemidef ∧ σ.trace = 1 ∧ (∑ i, conj (ψ1 i) * ψ1 i = 1) ∧
    entropyExchange Phi rho = vnEntropy σ ∧
    purificationFidelity psi Phi = (∑ a, ∑ b, conj (ψ1 a) * σ a b * ψ1 b).re := by
  intro σ
  have hP : Phi = krausApply A := funext hA
  have hσ : σ = Vm A ψ1 * (Vm A ψ1)ᴴ := idT_eq A ψ1
  refine ⟨hσ ▸ Matrix.posSemidef_self_mul_conjTranspose _, ?_, ?_, ?_, ?_⟩
  · rw [hσ, Matrix.trace_mul_comm, ← Matrix.trace_transpose, gram_eq A ψ1 rho hK0]
    have : (krausApply A rho).trace = rho.trace := by
      simp only [krausApply, Matrix.trace_sum]
      simp_rw [Matrix.trace_mul_cycle (A _) rho]
      rw [← Matrix.trace_sum, ← Finset.sum_mul, hKF, one_mul]
    rw [hrho.2] at this
    rw [← this]
    simp only [Matrix.trace, Matrix.diag, Matrix.of_apply, krausApply, Matrix.sum_apply]
    exact Finset.sum_comm
  · rw [Fintype.sum_prod_type, Finset.sum_comm]
    have : ∀ j, ∑ r, conj (ψ1 (r, j)) * ψ1 (r, j) = rho j j := fun j => by
      rw [← hK0]; exact Finset.sum_congr rfl fun r _ => mul_comm _ _
    simp only [this]
    exact hrho.2
  · rw [ent_exchange Phi A hA rho hrho.1, ent_core A ψ1 rho hK0]
  · rw [hP, X4P41L.kraus_fid]
    have h1 : traceLeft (pureDensity psi) = traceLeft (pureDensity ψ1) := by
      rw [hpsi.2]; ext j j'
      simp only [traceLeft, pureDensity, Matrix.of_apply]; exact (hK0 j j').symm
    rw [h1, ← X4P41L.kraus_fid]
    rfl

/-- a purification with reference dimension `rank ρ`. -/
lemma rank_purif {d : ℕ} (rho : Matrix (Fin d) (Fin d) ℂ) (hrho : rho.PosSemidef) :
    ∃ ψ1 : EuclideanSpace ℂ (Fin rho.rank × Fin d),
      ∀ j j', ∑ r, ψ1 (r, j) * conj (ψ1 (r, j')) = rho j j' := by
  set V := hrho.1.eigenvectorUnitary
  set lam := hrho.1.eigenvalues
  have hspec := hrho.1.spectral_theorem
  have hentry : ∀ p q, rho p q = ∑ k, (V : Matrix _ _ ℂ) p k * (lam k : ℂ) * conj ((V : Matrix _ _ ℂ) q k) := by
    intro p q
    have := congrFun (congrFun hspec p) q
    rw [this]
    simp only [Unitary.conjStarAlgAut_apply, Matrix.mul_apply, diagonal_apply, Function.comp_apply,
      star_apply, RCLike.star_def, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rfl
  have hcard := hrho.1.rank_eq_card_non_zero_eigs
  let e : Fin rho.rank ≃ {k // hrho.1.eigenvalues k ≠ 0} := (Fintype.equivFinOfCardEq hcard.symm).symm
  refine ⟨WithLp.toLp 2 fun z => ((Real.sqrt (lam (e z.1).1) : ℝ) : ℂ) * (V : Matrix _ _ ℂ) z.2 (e z.1).1, ?_⟩
  intro j j'
  rw [hentry]
  simp only [PiLp.toLp_apply, map_mul, Complex.conj_ofReal]
  have hsq : ∀ k, ((Real.sqrt (lam k) : ℝ) : ℂ) * ((Real.sqrt (lam k) : ℝ) : ℂ) = (lam k : ℂ) := by
    intro k; rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hrho.eigenvalues_nonneg k)]
  have h1 : ∑ r, ((Real.sqrt (lam (e r).1) : ℝ) : ℂ) * (V : Matrix _ _ ℂ) j (e r).1 *
      (((Real.sqrt (lam (e r).1) : ℝ) : ℂ) * conj ((V : Matrix _ _ ℂ) j' (e r).1)) =
      ∑ k : {k // lam k ≠ 0}, (V : Matrix _ _ ℂ) j k.1 * (lam k.1 : ℂ) * conj ((V : Matrix _ _ ℂ) j' k.1) := by
    refine Fintype.sum_equiv e _ _ fun r => ?_
    rw [← hsq]; ring
  rw [h1]
  rw [← Finset.sum_subtype (p := fun k => lam k ≠ 0) (Finset.univ.filter fun k => lam k ≠ 0)
    (by simp) (fun k => (V : Matrix _ _ ℂ) j k * (lam k : ℂ) * conj ((V : Matrix _ _ ℂ) j' k))]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs with h
  · rfl
  · push_neg at h; rw [h]; simp

lemma rank_ref {a d : ℕ} (psi : EuclideanSpace ℂ (Fin a × Fin d)) :
    (traceRight (pureDensity psi)).rank = (traceLeft (pureDensity psi)).rank := by
  set Ψ : Matrix (Fin a) (Fin d) ℂ := Matrix.of fun r j => psi (r, j)
  have h1 : traceRight (pureDensity psi) = Ψ * Ψᴴ := by
    ext r r'; simp [traceRight, pureDensity, Matrix.mul_apply, Ψ, conjTranspose_apply]
  have h2 : traceLeft (pureDensity psi) = (Ψᴴ * Ψ)ᵀ := by
    ext j j'; simp [traceLeft, pureDensity, Matrix.mul_apply, Ψ, conjTranspose_apply, mul_comm]
  rw [h1, h2, Matrix.rank_transpose, Matrix.rank_self_mul_conjTranspose,
    Matrix.rank_conjTranspose_mul_self]

end X4RF

end QAlgorithms.Papers.Independent.Support50.P41

end

-- ===== PFano =====

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P41

open QAlgorithms

open QAlgorithms.Entanglement (IsCompletelyPositive)

open QAlgorithms.Papers.Independent.Dependency50.P40 (IsPurification purificationFidelity)

open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange)

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)

open QAlgorithms.Papers.Independent.Information100.P34 (choi dephasing)

open QAlgorithms.Papers.Independent.Dependency50.P38 (vectorizeInputFirst)

open QAlgorithms.Papers.Independent.Gap20.P06 (dilationChannel environmentOutput dilatedVector)

open QAlgorithms.Papers.Independent.Information100.P50 (complementaryMap)

open QAlgorithms.Papers.Independent.Renew46.P43 (IsCountablePOVM classicalKLTerm countableEntropy)

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

-- The accepted generic dilation functions fix classical equality on each factor.
-- Match that instance for Fin before forming their product unitary groups.

local instance (priority := 2000) instPF (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _


namespace X4PF
open Matrix X4KF

lemma unitary_compact (d : ℕ) :
    IsCompact (Matrix.unitaryGroup (Fin d) ℂ : Set (Matrix (Fin d) (Fin d) ℂ)) := by
  have hK : IsCompact (Set.univ.pi fun _ : Fin d => Set.univ.pi fun _ : Fin d =>
      Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  refine hK.of_isClosed_subset ?_ ?_
  · have : (Matrix.unitaryGroup (Fin d) ℂ : Set (Matrix (Fin d) (Fin d) ℂ)) =
        (fun M : Matrix (Fin d) (Fin d) ℂ => star M * M) ⁻¹' {1} := by
      ext M; simp [Matrix.mem_unitaryGroup_iff']
    rw [this]
    exact isClosed_singleton.preimage (by fun_prop)
  · intro M hM
    simp only [Set.mem_pi, Set.mem_univ, Metric.mem_closedBall, dist_zero_right, true_implies]
    intro i j
    have h := (X4FN.ds_sums M hM).1 j
    have hle : Complex.normSq (M i j) ≤ 1 := by
      rw [← h]; exact Finset.single_le_sum (f := fun k => Complex.normSq (M k j))
        (fun k _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
    rw [Complex.normSq_eq_norm_sq] at hle
    nlinarith [norm_nonneg (M i j)]

lemma conj_kraus {d m : ℕ} (E : Fin m → Matrix (Fin d) (Fin d) ℂ) (V : Matrix (Fin d) (Fin d) ℂ) (X) :
    conjSuperop V (krausApply E X) = krausApply (fun k => V * E k) X := by
  simp only [conjSuperop, krausApply, Finset.mul_sum, Finset.sum_mul, conjTranspose_mul,
    Matrix.mul_assoc]

lemma kf_conj {d m : ℕ} (E : Fin m → Matrix (Fin d) (Fin d) ℂ) (hE : IsKrausFamily E)
    (V : Matrix (Fin d) (Fin d) ℂ) (hV : V ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    IsKrausFamily (fun k => V * E k) := by
  unfold IsKrausFamily at *
  have hV' : Vᴴ * V = 1 := Matrix.mem_unitaryGroup_iff'.1 hV
  simp only [conjTranspose_mul]
  rw [← hE]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ, hV', Matrix.one_mul]

lemma W_conj {d m : ℕ} (E : Fin m → Matrix (Fin d) (Fin d) ℂ) (V : Matrix (Fin d) (Fin d) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Fin d) ℂ) (rho : Matrix (Fin d) (Fin d) ℂ) :
    (Matrix.of fun k l => ((V * E k) * rho * (V * E l)ᴴ).trace) =
      Matrix.of fun k l => (E k * rho * (E l)ᴴ).trace := by
  ext k l
  have hV' : Vᴴ * V = 1 := Matrix.mem_unitaryGroup_iff'.1 hV
  simp only [Matrix.of_apply, conjTranspose_mul]
  rw [show V * E k * rho * ((E l)ᴴ * Vᴴ) = V * (E k * rho * (E l)ᴴ * Vᴴ) by
    simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc, hV', Matrix.mul_one]

end X4PF

open X4PF X4RF X4FN X4KF in
theorem _root_.solution {d a : ℕ} [NeZero d]
    (Phi : Superop (Fin d) (Fin d)) (hPhi : IsChannel Phi)
    (rho : Matrix (Fin d) (Fin d) ℂ) (hrho : IsDensityMatrix rho)
    (psi : EuclideanSpace ℂ (Fin a × Fin d)) (hpsi : IsPurification rho psi) :
    ∃ U : Matrix.unitaryGroup (Fin d) ℂ,
      let f := purificationFidelity psi (conjSuperop (U : Matrix (Fin d) (Fin d) ℂ) ∘ Phi)
      (∀ V : Matrix.unitaryGroup (Fin d) ℂ,
        purificationFidelity psi (conjSuperop (V : Matrix (Fin d) (Fin d) ℂ) ∘ Phi) ≤ f) ∧
      purificationFidelity psi Phi ≤ f ∧
      (∀ b (phi : EuclideanSpace ℂ (Fin b × Fin d)), IsPurification rho phi →
        ∀ V : Matrix.unitaryGroup (Fin d) ℂ,
          purificationFidelity phi (conjSuperop (V : Matrix (Fin d) (Fin d) ℂ) ∘ Phi) =
          purificationFidelity psi (conjSuperop (V : Matrix (Fin d) (Fin d) ℂ) ∘ Phi)) ∧
      (d = 1 → f = 1 ∧ entropyExchange Phi rho = 0) ∧
      (2 ≤ d → entropyExchange Phi rho ≤ binEntropy2 f + (1-f)*Real.logb 2 ((d : ℝ)^2-1)) ∧
      entropyExchange Phi rho ≤ 1+2*(1-f)*Real.logb 2 d := by
  obtain ⟨m, E, hKF, hE⟩ := hPhi
  have hcomp : ∀ V : Matrix (Fin d) (Fin d) ℂ,
      conjSuperop V ∘ Phi = krausApply (fun k => V * E k) := fun V => by
    funext X; simp only [Function.comp_apply, hE, conj_kraus]
  -- fidelity formula
  have hfid : ∀ b (phi : EuclideanSpace ℂ (Fin b × Fin d)), IsPurification rho phi →
      ∀ V : Matrix (Fin d) (Fin d) ℂ, purificationFidelity phi (conjSuperop V ∘ Phi) =
        ∑ k, Complex.normSq ((rho * (V * E k)).trace) := by
    intro b phi hphi V
    rw [hcomp, X4P41L.kraus_fid, hphi.2]
  set g : Matrix (Fin d) (Fin d) ℂ → ℝ := fun V => ∑ k, Complex.normSq ((rho * (V * E k)).trace)
  have hg : Continuous g := by
    refine continuous_finsetSum _ fun k _ => Complex.continuous_normSq.comp ?_
    exact (continuous_const.matrix_mul (continuous_id.matrix_mul continuous_const)).matrix_trace
  have hne : (Matrix.unitaryGroup (Fin d) ℂ : Set (Matrix (Fin d) (Fin d) ℂ)).Nonempty :=
    ⟨1, one_mem _⟩
  obtain ⟨U0, hU0, hmax⟩ := (unitary_compact d).exists_isMaxOn hne hg.continuousOn
  refine ⟨⟨U0, hU0⟩, ?_⟩
  intro f
  have hf : f = g U0 := hfid a psi hpsi U0
  -- entropy is unchanged by the unitary
  have hSe : entropyExchange Phi rho = entropyExchange (conjSuperop U0 ∘ Phi) rho := by
    rw [ent_exchange Phi E hE rho hrho.1,
      ent_exchange _ (fun k => U0 * E k) (fun X => by rw [hcomp]) rho hrho.1, W_conj E U0 hU0]
  obtain ⟨hpsd, htr, hψ, hS, hF⟩ := core (conjSuperop U0 ∘ Phi) (fun k => U0 * E k)
    (kf_conj E hKF U0 hU0) (fun X => by rw [hcomp]) rho hrho psi hpsi
    (WithLp.toLp 2 fun z => cfc Real.sqrt rho z.2 z.1 : EuclideanSpace ℂ (Fin d × Fin d)) (fun j j' => sqrt_gram rho hrho.1 j j')
  rw [← hSe] at hS
  have hfF : f = _ := hF
  have hone : d = 1 → f = 1 ∧ entropyExchange Phi rho = 0 := by
    intro h1
    rw [hS, hfF]
    exact fano_one hpsd htr _ hψ (by simp [h1])
  have htwo : 2 ≤ d → (f ≤ 1) ∧
      entropyExchange Phi rho ≤ binEntropy2 f + (1 - f) * Real.logb 2 ((d : ℝ)^2 - 1) := by
    intro h2
    have hN : 2 ≤ Fintype.card (Fin d × Fin d) := by
      simp only [Fintype.card_prod, Fintype.card_fin]; nlinarith
    have := fano hpsd htr _ hψ hN
    rw [hS, hfF]
    simpa [Fintype.card_prod, Fintype.card_fin, sq] using this
  refine ⟨fun V => ?_, ?_, fun b phi hphi V => by rw [hfid b phi hphi, hfid a psi hpsi], hone,
    fun h => (htwo h).2, ?_⟩
  · rw [hfid a psi hpsi, hf]; exact hmax V.2
  · have h1 : purificationFidelity psi Phi = g 1 := by
      have := hfid a psi hpsi 1
      have e1 : conjSuperop (1 : Matrix (Fin d) (Fin d) ℂ) ∘ Phi = Phi := by
        funext X; simp [conjSuperop]
      rw [e1] at this; exact this
    rw [h1, hf]; exact hmax (one_mem _)
  · rcases Nat.lt_or_ge d 2 with hd | hd
    · have h1 : d = 1 := by have := NeZero.ne d; omega
      obtain ⟨hF1, hS0⟩ := hone h1
      rw [hF1, hS0, h1]; norm_num
    · obtain ⟨hF1, hb⟩ := htwo hd
      refine hb.trans ?_
      have hbin : binEntropy2 f ≤ 1 := by
        unfold binEntropy2
        rw [div_le_one (Real.log_pos (by norm_num))]
        exact Real.binEntropy_le_log_two
      have hD : (2:ℝ) ≤ d := by exact_mod_cast hd
      have hlog : Real.logb 2 ((d : ℝ)^2 - 1) ≤ 2 * Real.logb 2 d := by
        rw [← Real.logb_rpow_eq_mul_logb_of_pos (by linarith)]
        refine Real.logb_le_logb_of_le (by norm_num) (by nlinarith) ?_
        norm_num
      have h0 : 0 ≤ 1 - f := by linarith
      nlinarith [mul_le_mul_of_nonneg_left hlog h0]

end QAlgorithms.Papers.Independent.Support50.P41

end

#print axioms solution
