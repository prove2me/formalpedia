-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P42.local_entropy_bounds
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T18:47:17.644011+00:00
-- url     : https://prove2.me/submissions/4deb6d4e-14e6-411f-b74c-267a133cca40

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P42
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P41
import Definitions.Def_QAlgorithms_Defs_QuantumInformation

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

end

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

end

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

end

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

end

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

end

-- ===== SFB =====

/-! Generic: `Σ_k |tr(ρ E_k)|² ≤ F(ρ, Σ_k E_k ρ E_kᴴ)²` for PSD `ρ`. -/

noncomputable section

namespace X4SF
open Matrix QAlgorithms
open scoped Matrix ComplexOrder ComplexConjugate

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Fintype K]

lemma sq_sqrt (ρ : Matrix ι ι ℂ) (h : ρ.PosSemidef) : cfc Real.sqrt ρ * cfc Real.sqrt ρ = ρ := by
  open scoped MatrixOrder in
  have h0 : 0 ≤ ρ := h.nonneg
  have := CFC.sqrt_mul_sqrt_self ρ h0
  rwa [CFC.sqrt_eq_real_sqrt ρ h0, cfcₙ_eq_cfc] at this

lemma herm_sqrt (ρ : Matrix ι ι ℂ) : (cfc Real.sqrt ρ).IsHermitian :=
  (cfc_predicate Real.sqrt ρ : IsSelfAdjoint _)

lemma cfc_trace {Y : Matrix ι ι ℂ} (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma diag_of {Y : Matrix ι ι ℂ} (hY : Y.IsHermitian) :
    star (hY.eigenvectorUnitary : Matrix ι ι ℂ) * Y * (hY.eigenvectorUnitary : Matrix ι ι ℂ) =
      diagonal (fun i => ((hY.eigenvalues i : ℝ) : ℂ)) := by
  set U : Matrix ι ι ℂ := (hY.eigenvectorUnitary : Matrix ι ι ℂ)
  have hU : star U * U = 1 := Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2
  conv_lhs => rw [hY.spectral_theorem, Unitary.conjStarAlgAut_apply]
  change star U * (U * _ * star U) * U = _
  rw [show star U * (U * diagonal (RCLike.ofReal ∘ hY.eigenvalues) * star U) * U =
    (star U * U) * diagonal (RCLike.ofReal ∘ hY.eigenvalues) * (star U * U) by
      simp only [Matrix.mul_assoc]]
  rw [hU, Matrix.one_mul, Matrix.mul_one]
  rfl

theorem key (ρ : Matrix ι ι ℂ) (hρ : ρ.PosSemidef) (E : K → Matrix ι ι ℂ) :
    ∑ k, Complex.normSq ((ρ * E k).trace) ≤ rootFidelity ρ (∑ k, E k * ρ * (E k)ᴴ) ^ 2 := by
  set R := cfc Real.sqrt ρ with hRdef
  have hR : Rᴴ = R := herm_sqrt ρ
  have hRR : R * R = ρ := sq_sqrt ρ hρ
  set H := R * (∑ k, E k * ρ * (E k)ᴴ) * R with hHdef
  have hHpsd : H.PosSemidef := by
    have : (∑ k, E k * ρ * (E k)ᴴ).PosSemidef :=
      Matrix.posSemidef_sum _ fun k _ => hρ.mul_mul_conjTranspose_same (E k)
    have := this.conjTranspose_mul_mul_same R
    rwa [hR] at this
  have hH : H.IsHermitian := hHpsd.1
  set U : Matrix ι ι ℂ := (hH.eigenvectorUnitary : Matrix ι ι ℂ)
  have hD : Uᴴ * H * U = diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) := by
    rw [← Matrix.star_eq_conjTranspose]; exact diag_of hH
  have hU' : U * Uᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Unitary.mul_star_self_of_mem hH.eigenvectorUnitary.2
  set lam := hH.eigenvalues
  set G : K → Matrix ι ι ℂ := fun k => Uᴴ * (R * E k * R) * U
  have e : ∀ k, G k * (G k)ᴴ = Uᴴ * (R * (E k * ρ * (E k)ᴴ) * R) * U := by
    intro k
    simp only [G, Matrix.conjTranspose_mul, hR, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U Uᴴ, hU', Matrix.one_mul, ← Matrix.mul_assoc R R, hRR]
  have hGG : ∑ k, G k * (G k)ᴴ = diagonal (fun i => ((lam i : ℝ) : ℂ)) := by
    rw [← hD, Finset.sum_congr rfl fun k _ => e k, ← Finset.sum_mul, ← Matrix.mul_sum,
      ← Finset.sum_mul, ← Matrix.mul_sum, hHdef]
  have htr : ∀ k, (ρ * E k).trace = ∑ i, G k i i := by
    intro k
    change _ = (G k).trace
    rw [show G k = Uᴴ * (R * E k * R) * U from rfl, Matrix.trace_mul_cycle,
      hU', Matrix.one_mul, ← hRR, Matrix.mul_assoc, Matrix.trace_mul_comm R]
  have hrow : ∀ i, ∑ k, Complex.normSq (G k i i) ≤ lam i := by
    intro i
    have h1 := congrArg (fun M => (M i i).re) hGG
    simp only [Matrix.sum_apply, Matrix.diagonal_apply_eq, Complex.ofReal_re, Complex.re_sum,
      Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def, Complex.mul_conj] at h1
    rw [← h1]
    refine Finset.sum_le_sum fun k _ => ?_
    exact Finset.single_le_sum (f := fun j => Complex.normSq (G k i j))
      (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  have hRF : rootFidelity ρ (∑ k, E k * ρ * (E k)ᴴ) = ∑ i, Real.sqrt (lam i) := by
    unfold rootFidelity
    rw [← hRdef, ← hHdef, cfc_trace hH, Complex.re_sum]
    simp [lam]
  -- triangle inequality in ℓ²(K)
  let a : ι → EuclideanSpace ℂ K := fun i => WithLp.toLp 2 fun k => G k i i
  have hna : ∀ i, ‖a i‖ ≤ Real.sqrt (lam i) := by
    intro i
    rw [EuclideanSpace.norm_eq]
    refine Real.sqrt_le_sqrt ?_
    refine le_trans (le_of_eq ?_) (hrow i)
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [a, Complex.sq_norm]
  have hsum : ‖∑ i, a i‖ ≤ ∑ i, Real.sqrt (lam i) :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hna i)
  have hlhs : ∑ k, Complex.normSq ((ρ * E k).trace) = ‖∑ i, a i‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [htr k, ← Complex.sq_norm]
    simp [a, WithLp.ofLp_sum]
  rw [hlhs, hRF]
  exact pow_le_pow_left₀ (norm_nonneg _) hsum 2

end X4SF

end

-- ===== SUB =====

/-! Generic: subadditivity of von Neumann entropy, `S(AB) ≤ S(A) + S(B)`. -/

noncomputable section

namespace X4SU
open Matrix Real QAlgorithms
open scoped Matrix ComplexConjugate ComplexOrder Kronecker

/-- one term of the classical bound. -/
lemma term {r a b : ℝ} (hr : 0 ≤ r) (ha : r ≤ a) (hb : r ≤ b) :
    negMulLog r ≤ -(r * Real.log a) - r * Real.log b + a * b - r := by
  rcases hr.eq_or_lt with rfl | hr
  · simp; exact mul_nonneg (by linarith) (by linarith)
  · have ha' : 0 < a := hr.trans_le ha
    have hb' : 0 < b := hr.trans_le hb
    have hx : 0 < a * b / r := by positivity
    have h := Real.log_le_sub_one_of_pos hx
    rw [Real.log_div (by positivity) hr.ne', Real.log_mul ha'.ne' hb'.ne'] at h
    have h2 := mul_le_mul_of_nonneg_left h hr.le
    rw [show r * (a * b / r - 1) = a * b - r by field_simp] at h2
    simp only [negMulLog]
    nlinarith

/-- classical subadditivity of Shannon entropy. -/
lemma classical {A B : Type*} [Fintype A] [Fintype B] (r : A × B → ℝ) (h0 : ∀ p, 0 ≤ r p)
    (h1 : ∑ p, r p = 1) :
    ∑ p, negMulLog (r p) ≤ ∑ i, negMulLog (∑ j, r (i, j)) + ∑ j, negMulLog (∑ i, r (i, j)) := by
  have hle : ∀ p, negMulLog (r p) ≤ -(r p * Real.log (∑ j, r (p.1, j))) -
      r p * Real.log (∑ i, r (i, p.2)) + (∑ j, r (p.1, j)) * (∑ i, r (i, p.2)) - r p := by
    intro p
    refine term (h0 p) ?_ ?_
    · exact Finset.single_le_sum (f := fun j => r (p.1, j)) (fun j _ => h0 _) (Finset.mem_univ p.2)
    · exact Finset.single_le_sum (f := fun i => r (i, p.2)) (fun i _ => h0 _) (Finset.mem_univ p.1)
  refine (Finset.sum_le_sum fun p _ => hle p).trans (le_of_eq ?_)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  have e1 : ∑ p : A × B, r p * Real.log (∑ j, r (p.1, j)) = ∑ i, (∑ j, r (i, j)) * Real.log (∑ j, r (i, j)) := by
    rw [Fintype.sum_prod_type]; simp [Finset.sum_mul]
  have e2 : ∑ p : A × B, r p * Real.log (∑ i, r (i, p.2)) = ∑ j, (∑ i, r (i, j)) * Real.log (∑ i, r (i, j)) := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]; simp [Finset.sum_mul]
  have e3 : ∑ p : A × B, (∑ j, r (p.1, j)) * (∑ i, r (i, p.2)) = 1 := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
    rw [Finset.sum_comm (f := fun i y => r (y, i))]
    have : ∑ x, ∑ y, r (x, y) = 1 := by rw [← h1, Fintype.sum_prod_type]
    rw [this]; ring
  rw [e1, e2, e3, h1]
  simp only [negMulLog, neg_mul, Finset.sum_neg_distrib]
  ring

lemma pull4 {α β γ δ M : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [AddCommMonoid M]
    (f : α → β → γ → δ → M) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ b, ∑ c, ∑ d, ∑ a, f a b c d := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

lemma marg_left (ω : Matrix (A × B) (A × B) ℂ) (UA : Matrix A A ℂ) (UB : Matrix B B ℂ)
    (hUB : UB * UBᴴ = 1) (i : A) :
    ∑ j, ((UA ⊗ₖ UB)ᴴ * ω * (UA ⊗ₖ UB)) (i, j) (i, j) = (UAᴴ * traceRight ω * UA) i i := by
  have hd : ∀ s t : B, ∑ j, conj (UB s j) * UB t j = if t = s then 1 else 0 := by
    intro s t
    have := congrFun (congrFun hUB t) s
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [conjTranspose_apply, RCLike.star_def, mul_comm]
  simp only [Matrix.mul_apply, conjTranspose_apply, kroneckerMap_apply, traceRight, Matrix.of_apply,
    RCLike.star_def, map_mul, Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun x _ => ?_)
  rw [pull4]
  have e : ∀ (x1 : B) (x2 : A) (x3 : B), ∑ j, conj (UA x2 i) * conj (UB x3 j) * ω (x2, x3) (x, x1) *
      (UA x i * UB x1 j) = conj (UA x2 i) * ω (x2, x3) (x, x1) * UA x i * (if x1 = x3 then 1 else 0) := by
    intro x1 x2 x3
    rw [← hd x3 x1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [e, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact Finset.sum_comm

lemma marg_right (ω : Matrix (A × B) (A × B) ℂ) (UA : Matrix A A ℂ) (UB : Matrix B B ℂ)
    (hUA : UA * UAᴴ = 1) (j : B) :
    ∑ i, ((UA ⊗ₖ UB)ᴴ * ω * (UA ⊗ₖ UB)) (i, j) (i, j) = (UBᴴ * traceLeft ω * UB) j j := by
  have hd : ∀ s t : A, ∑ i, conj (UA s i) * UA t i = if t = s then 1 else 0 := by
    intro s t
    have := congrFun (congrFun hUA t) s
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [conjTranspose_apply, RCLike.star_def, mul_comm]
  simp only [Matrix.mul_apply, conjTranspose_apply, kroneckerMap_apply, traceLeft, Matrix.of_apply,
    RCLike.star_def, map_mul, Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
  rw [pull4]
  have e : ∀ (b : A) (c : B) (d : A), ∑ a, ∑ x, conj (UA d a) * conj (UB x j) * ω (d, x) (b, c) *
      (UA b a * UB c j) = (∑ x, conj (UB x j) * ω (d, x) (b, c) * UB c j) * (if b = d then 1 else 0) := by
    intro b c d
    rw [Finset.sum_comm, ← hd d b, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  simp_rw [e, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]

lemma herm_right {ω : Matrix (A × B) (A × B) ℂ} (h : ω.IsHermitian) : (traceRight ω).IsHermitian := by
  ext i j
  have := fun s => congrFun (congrFun h (i, s)) (j, s)
  simp only [conjTranspose_apply, traceRight, Matrix.of_apply, star_sum] at this ⊢
  exact Finset.sum_congr rfl fun s _ => this s

lemma herm_left {ω : Matrix (A × B) (A × B) ℂ} (h : ω.IsHermitian) : (traceLeft ω).IsHermitian := by
  ext i j
  have := fun s => congrFun (congrFun h (s, i)) (s, j)
  simp only [conjTranspose_apply, traceLeft, Matrix.of_apply, star_sum] at this ⊢
  exact Finset.sum_congr rfl fun s _ => this s

/-- subadditivity of von Neumann entropy. -/
theorem subadd (ω : Matrix (A × B) (A × B) ℂ) (hω : ω.PosSemidef) (htr : ω.trace = 1) :
    vnEntropy ω ≤ vnEntropy (traceRight ω) + vnEntropy (traceLeft ω) := by
  have hA := herm_right hω.1
  have hB := herm_left hω.1
  set UA : Matrix A A ℂ := (hA.eigenvectorUnitary : Matrix A A ℂ)
  set UB : Matrix B B ℂ := (hB.eigenvectorUnitary : Matrix B B ℂ)
  have hUA : UA * UAᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2
  have hUB : UB * UBᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Unitary.mul_star_self_of_mem hB.eigenvectorUnitary.2
  have hU : UA ⊗ₖ UB ∈ Matrix.unitaryGroup (A × B) ℂ :=
    Matrix.kronecker_mem_unitary hA.eigenvectorUnitary.2 hB.eigenvectorUnitary.2
  obtain ⟨h0, h1, h2⟩ := X4FN.schur hω _ hU
  set r : A × B → ℝ := fun p => (((UA ⊗ₖ UB)ᴴ * ω * (UA ⊗ₖ UB)) p p).re with hr
  have hra : ∀ i, ∑ j, r (i, j) = hA.eigenvalues i := by
    intro i
    simp only [r]
    rw [← Complex.re_sum, marg_left ω UA UB hUB i, ← Matrix.star_eq_conjTranspose, X4SF.diag_of hA,
      diagonal_apply_eq, Complex.ofReal_re]
  have hrb : ∀ j, ∑ i, r (i, j) = hB.eigenvalues j := by
    intro j
    simp only [r]
    rw [← Complex.re_sum, marg_right ω UA UB hUA j, ← Matrix.star_eq_conjTranspose, X4SF.diag_of hB,
      diagonal_apply_eq, Complex.ofReal_re]
  have hc := classical r h0 (by rw [h1, htr, Complex.one_re])
  simp only [hra, hrb] at hc
  rw [X4FN.vn_eig hA, X4FN.vn_eig hB, ← add_div]
  refine h2.trans (div_le_div_of_nonneg_right hc (Real.log_pos (by norm_num)).le)

end X4SU

end

-- ===== ZEA =====

noncomputable section

namespace X4ZE
open Matrix QAlgorithms Real
open scoped Matrix ComplexConjugate ComplexOrder

/-- a unit vector `v` with `v v† = Σ φ_k φ_k†` forces every `φ_k ∈ span v`. -/
lemma rank1_split {α ι : Type*} [Fintype α] [Fintype ι] (v : α → ℂ) (hv : ∑ a, v a * conj (v a) = 1)
    (φ : ι → α → ℂ) (h : ∀ a b, v a * conj (v b) = ∑ k, φ k a * conj (φ k b)) (k : ι) :
    ∀ a, φ k a = (∑ b, conj (v b) * φ k b) * v a := by
  set c := ∑ b, conj (v b) * φ k b
  set ψ : α → ℂ := fun a => φ k a - c * v a
  have nsq : ∀ u w : α → ℂ, ((Complex.normSq (∑ a, conj (u a) * w a) : ℝ) : ℂ) =
      ∑ a, ∑ b, conj (u a) * (w a * conj (w b)) * u b := by
    intro u w
    rw [Complex.normSq_eq_conj_mul_self, map_sum, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [map_mul, Complex.conj_conj]; ring
  have hQ : ∀ ψ : α → ℂ, Complex.normSq (∑ a, conj (ψ a) * v a) =
      ∑ j, Complex.normSq (∑ a, conj (ψ a) * φ j a) := by
    intro ψ
    have : ((Complex.normSq (∑ a, conj (ψ a) * v a) : ℝ) : ℂ) =
        ((∑ j, Complex.normSq (∑ a, conj (ψ a) * φ j a) : ℝ) : ℂ) := by
      rw [nsq]; push_cast; simp_rw [nsq, h, Finset.mul_sum, Finset.sum_mul]
      calc ∑ a, ∑ b, ∑ j, conj (ψ a) * (φ j a * conj (φ j b)) * ψ b
          = ∑ a, ∑ j, ∑ b, conj (ψ a) * (φ j a * conj (φ j b)) * ψ b :=
            Finset.sum_congr rfl fun a _ => Finset.sum_comm
        _ = _ := Finset.sum_comm
    exact_mod_cast this
  have hψv : ∑ a, conj (ψ a) * v a = 0 := by
    have : ∑ a, conj (v a) * ψ a = 0 := by
      simp only [ψ, mul_sub, Finset.sum_sub_distrib]
      have : ∑ a, conj (v a) * (c * v a) = c * ∑ a, v a * conj (v a) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => by ring
      rw [this, hv, mul_one]; simp [c]
    have := congrArg conj this
    rw [map_sum, map_zero] at this
    rw [← this]; exact Finset.sum_congr rfl fun a _ => by simp [mul_comm]
  have hψφ : ∑ a, conj (ψ a) * φ k a = ∑ a, conj (ψ a) * ψ a := by
    have : ∀ a, φ k a = ψ a + c * v a := fun a => by simp [ψ]
    simp_rw [this, mul_add, Finset.sum_add_distrib]
    have : ∑ a, conj (ψ a) * (c * v a) = c * ∑ a, conj (ψ a) * v a := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => by ring
    rw [this, hψv, mul_zero, add_zero]
  have hz := hQ ψ
  rw [hψv, map_zero] at hz
  have hk := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg _)).1 hz.symm k
    (Finset.mem_univ k)
  rw [hψφ, Complex.normSq_eq_zero] at hk
  have hn : ∑ a, Complex.normSq (ψ a) = 0 := by
    have : ((∑ a, Complex.normSq (ψ a) : ℝ) : ℂ) = 0 := by
      push_cast; rw [← hk]
      exact Finset.sum_congr rfl fun a _ => by rw [Complex.normSq_eq_conj_mul_self]
    exact_mod_cast this
  intro a
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => Complex.normSq_nonneg _)).1 hn a
    (Finset.mem_univ a)
  rw [Complex.normSq_eq_zero] at this
  simp only [ψ, sub_eq_zero] at this
  exact this

/-- spectral decomposition as a sum of eigenprojectors. -/
lemma spec_sum {I : Type*} [Fintype I] [DecidableEq I] {ρ : Matrix I I ℂ} (h : ρ.IsHermitian) :
    ρ = ∑ k, ((h.eigenvalues k : ℝ) : ℂ) • pureDensity (h.eigenvectorBasis k) := by
  conv_lhs => rw [h.spectral_theorem, Unitary.conjStarAlgAut_apply]
  ext a b
  simp only [Matrix.mul_apply, diagonal, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply,
    pureDensity, smul_eq_mul, Function.comp_apply, Matrix.star_apply, RCLike.star_def,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, ite_mul, zero_mul,
    Finset.sum_ite_eq, Matrix.IsHermitian.eigenvectorUnitary_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [RCLike.ofReal_eq_complex_ofReal]
  ring

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

/-- zero entropy density matrix is a pure projector. -/
lemma pure_of_vn {I : Type*} [Fintype I] [DecidableEq I] {ρ : Matrix I I ℂ} (hρ : ρ.PosSemidef)
    (h1 : ρ.trace = 1) (h0 : vnEntropy ρ = 0) :
    ∃ w : EuclideanSpace ℂ I, ‖w‖ = 1 ∧ ρ = pureDensity w := by
  set h := hρ.1
  set lam := h.eigenvalues
  set v := h.eigenvectorBasis
  have hv : ∀ k, ‖v k‖ = 1 := fun k => v.orthonormal.1 k
  have hl0 : ∀ k, 0 ≤ lam k := hρ.eigenvalues_nonneg
  have hsum : ∑ k, lam k = 1 := by
    have := h.trace_eq_sum_eigenvalues
    rw [h1] at this
    have h3 : ((∑ k, lam k : ℝ) : ℂ) = 1 := by push_cast; exact this.symm
    exact_mod_cast h3
  have hle1 : ∀ k, lam k ≤ 1 := fun k => by
    rw [← hsum]; exact Finset.single_le_sum (fun j _ => hl0 j) (Finset.mem_univ k)
  have hS : ∑ k, negMulLog (lam k) = 0 := by
    rw [vn_eig h] at h0
    rcases div_eq_zero_iff.1 h0 with h0 | h0
    · exact h0
    · exfalso; exact (Real.log_pos (by norm_num : (1:ℝ) < 2)).ne' h0
  have h01 : ∀ k, lam k = 0 ∨ lam k = 1 := by
    intro k
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Real.negMulLog_nonneg (hl0 j) (hle1 j))).1
      hS k (Finset.mem_univ k)
    rcases (hl0 k).eq_or_lt with h | h
    · exact Or.inl h.symm
    rcases (hle1 k).eq_or_lt with h' | h'
    · exact Or.inr h'
    exfalso
    have : lam k * Real.log (lam k) < 0 := mul_neg_of_pos_of_neg h (Real.log_neg h h')
    rw [Real.negMulLog] at *; linarith
  obtain ⟨i0, hi0⟩ : ∃ i0, lam i0 = 1 := by
    by_contra hc
    push Not at hc
    have : ∑ k, lam k = 0 := Finset.sum_eq_zero fun k _ => (h01 k).resolve_right (hc k)
    linarith
  have hother : ∀ k, k ≠ i0 → lam k = 0 := by
    have hs := Finset.add_sum_erase Finset.univ lam (Finset.mem_univ i0)
    rw [hsum, hi0] at hs
    have h0 : ∑ k ∈ Finset.univ.erase i0, lam k = 0 := by linarith
    intro k hk
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hl0 k)).1 h0 k
      (Finset.mem_erase.2 ⟨hk, Finset.mem_univ k⟩)
  refine ⟨v i0, hv i0, ?_⟩
  rw [spec_sum h]
  rw [Finset.sum_eq_single i0 (fun k _ hk => by simp [lam, hother k hk]) (by simp)]
  simp [lam, hi0]
  rfl

lemma unit_sum {I : Type*} [Fintype I] (v : EuclideanSpace ℂ I) (hv : ‖v‖ = 1) :
    ∑ i, v i * conj (v i) = 1 := by
  have h1 : ∑ i, ‖v i‖ ^ 2 = 1 := by
    rw [← EuclideanSpace.norm_sq_eq, hv, one_pow]
  have : ∑ i, v i * conj (v i) = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
  rw [this, h1]; simp

end X4ZE

end

-- ===== LEA =====

/-! Generic von Neumann entropy facts: scaling, orthogonal rank-one sums, `S(Σσ) ≤ ΣS(σ)`
for unnormalized PSD terms, and concavity `Σ (S(σ_m) + p_m log p_m) ≤ S(Σσ)`. -/

noncomputable section

namespace X4LE
open Matrix Real QAlgorithms
open scoped Matrix ComplexConjugate ComplexOrder

lemma cfc_diag {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℝ) (f : ℝ → ℝ) :
    cfc f (diagonal (fun i => (d i : ℂ))) = diagonal (fun i => (f (d i) : ℂ)) := by
  classical
  let S : Finset ℝ := Finset.univ.image d
  let p : Polynomial ℝ := Lagrange.interpolate S id f
  have hp : ∀ x ∈ S, p.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := id) (r := f) (Set.injOn_id _) hx
  have hD : IsSelfAdjoint (diagonal (fun i => (d i : ℂ))) := by
    rw [IsSelfAdjoint, star_eq_conjTranspose, diagonal_conjTranspose]
    congr 1; funext i; simp
  have hspec : ∀ x ∈ spectrum ℝ (diagonal (fun i => (d i : ℂ))), x ∈ S := by
    intro x hx
    rw [← spectrum.preimage_algebraMap ℂ, Set.mem_preimage, spectrum_diagonal] at hx
    obtain ⟨i, hi⟩ := hx
    have : d i = x := by simpa using hi
    simp [S, ← this]
  rw [cfc_congr (g := fun x => p.eval x) (fun x hx => (hp x (hspec x hx)).symm),
    cfc_polynomial p _ hD]
  have : Polynomial.aeval (diagonal (fun i => (d i : ℂ))) p =
      diagonal (Polynomial.aeval (fun i => (d i : ℂ)) p) :=
    (Polynomial.aeval_algHom_apply (diagonalAlgHom ℝ) (fun i => (d i : ℂ)) p)
  rw [this, Polynomial.aeval_pi_apply]
  congr 1; funext i
  have h := Polynomial.aeval_algebraMap_apply ℂ (d i) p
  simp only [Complex.coe_algebraMap] at h
  rw [h, Polynomial.coe_aeval_eq_eval, hp _ (by simp [S] : d i ∈ S)]

lemma vn_diag {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → ℝ) :
    vnEntropy (diagonal fun i => (x i : ℂ)) = -∑ i, x i * Real.logb 2 (x i) := by
  unfold vnEntropy
  rw [cfc_diag, Matrix.trace_diagonal, Complex.re_sum]
  simp

lemma nml (x : ℝ) : negMulLog x / Real.log 2 = -(x * Real.logb 2 x) := by
  simp only [negMulLog, Real.logb]; ring

lemma cont_xlog : Continuous (fun x : ℝ => x * Real.logb 2 x) := by
  have : (fun x : ℝ => x * Real.logb 2 x) = fun x => (x * Real.log x) / Real.log 2 := by
    funext x; rw [Real.logb]; ring
  rw [this]; exact Real.continuous_mul_log.div_const _

/-- scaling of the (unnormalized) entropy. -/
lemma vn_smul {ι : Type*} [Fintype ι] [DecidableEq ι] {X : Matrix ι ι ℂ} (hX : X.IsHermitian)
    {c : ℝ} (hc : 0 < c) :
    vnEntropy ((c : ℂ) • X) = c * vnEntropy X - c * Real.logb 2 c * X.trace.re := by
  have hsa : IsSelfAdjoint X := hX
  have e1 : (c : ℂ) • X = c • X := by rw [Complex.coe_smul]
  unfold vnEntropy
  rw [e1, ← cfc_comp_smul c (fun x : ℝ => x * Real.logb 2 x) X cont_xlog.continuousOn]
  have hf : ∀ x : ℝ, (c • x) * Real.logb 2 (c • x) =
      (c * Real.logb 2 c) * x + c * (x * Real.logb 2 x) := by
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · rw [smul_eq_mul, Real.logb_mul hc.ne' hx]; ring
  rw [cfc_congr (g := fun x => (c * Real.logb 2 c) * x + c * (x * Real.logb 2 x))
    (fun x _ => hf x)]
  rw [cfc_add (a := X) (fun x => (c * Real.logb 2 c) * x) (fun x => c * (x * Real.logb 2 x))
    (by fun_prop) ((continuous_const.mul cont_xlog).continuousOn),
    cfc_const_mul_id (c * Real.logb 2 c) X, cfc_const_mul c (fun x => x * Real.logb 2 x) X cont_xlog.continuousOn]
  simp only [Matrix.trace_add, Matrix.trace_smul, Complex.add_re, Complex.real_smul,
    Complex.re_ofReal_mul]
  ring

/-- entropy of a sum of mutually orthogonal rank-one terms. -/
lemma orth_ent {ι T : Type} [Fintype ι] [DecidableEq ι] [Fintype T] [DecidableEq T]
    (φ : T → ι → ℂ) (h : ∀ t t', t ≠ t' → ∑ i, φ t i * conj (φ t' i) = 0) :
    vnEntropy (∑ t, Matrix.of fun a b => φ t a * conj (φ t b)) =
      -∑ t, (∑ i, ‖φ t i‖ ^ 2) * Real.logb 2 (∑ i, ‖φ t i‖ ^ 2) := by
  set V : Matrix ι T ℂ := Matrix.of fun i t => φ t i
  have hV : (∑ t, Matrix.of fun a b => φ t a * conj (φ t b)) = V * Vᴴ := by
    ext a b; simp [V, Matrix.mul_apply, Matrix.sum_apply, conjTranspose_apply]
  rw [hV, X4KF.x4_ent_swap]
  have hD : (Vᴴ * V)ᵀ = diagonal fun t => ((∑ i, ‖φ t i‖ ^ 2 : ℝ) : ℂ) := by
    ext t t'
    simp only [transpose_apply, Matrix.mul_apply, conjTranspose_apply, V, Matrix.of_apply,
      diagonal_apply, RCLike.star_def]
    split_ifs with htt
    · subst htt; push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
    · rw [← h t t' htt]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [hD, vn_diag]

/-- square-root eigen-amplitudes of a PSD matrix. -/
def amp {ι : Type} [Fintype ι] [DecidableEq ι] {σ : Matrix ι ι ℂ} (hσ : σ.PosSemidef) (k a : ι) : ℂ :=
  ((Real.sqrt (hσ.1.eigenvalues k) : ℝ) : ℂ) * hσ.1.eigenvectorBasis k a

lemma amp_decomp {ι : Type} [Fintype ι] [DecidableEq ι] {σ : Matrix ι ι ℂ} (hσ : σ.PosSemidef) :
    σ = ∑ k, Matrix.of fun a b => amp hσ k a * conj (amp hσ k b) := by
  conv_lhs => rw [X4ZE.spec_sum hσ.1]
  refine Finset.sum_congr rfl fun k _ => ?_
  ext a b
  have hs : ((Real.sqrt (hσ.1.eigenvalues k) : ℝ) : ℂ) * ((Real.sqrt (hσ.1.eigenvalues k) : ℝ) : ℂ) =
      ((hσ.1.eigenvalues k : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hσ.eigenvalues_nonneg k)]
  simp only [Matrix.smul_apply, pureDensity, Matrix.of_apply, smul_eq_mul, amp, map_mul,
    Complex.conj_ofReal]
  rw [← hs]; ring

lemma amp_inner {ι : Type} [Fintype ι] [DecidableEq ι] {σ : Matrix ι ι ℂ} (hσ : σ.PosSemidef)
    (k k' : ι) : ∑ a, amp hσ k a * conj (amp hσ k' a) =
      if k = k' then ((hσ.1.eigenvalues k : ℝ) : ℂ) else 0 := by
  have ho := hσ.1.eigenvectorBasis.orthonormal
  have hin : ∑ a, hσ.1.eigenvectorBasis k a * conj (hσ.1.eigenvectorBasis k' a) =
      if k = k' then 1 else 0 := by
    have := orthonormal_iff_ite.1 ho k' k
    rw [EuclideanSpace.inner_eq_star_dotProduct] at this
    have e : (if k = k' then (1:ℂ) else 0) = if k' = k then 1 else 0 := by
      by_cases h : k = k' <;> simp [h, eq_comm]
    rw [e, ← this]
    simp [dotProduct, mul_comm]
  simp only [amp, map_mul, Complex.conj_ofReal]
  have : ∀ a, ((Real.sqrt (hσ.1.eigenvalues k) : ℝ) : ℂ) * hσ.1.eigenvectorBasis k a *
      (((Real.sqrt (hσ.1.eigenvalues k') : ℝ) : ℂ) * conj (hσ.1.eigenvectorBasis k' a)) =
      (((Real.sqrt (hσ.1.eigenvalues k) : ℝ) : ℂ) * ((Real.sqrt (hσ.1.eigenvalues k') : ℝ) : ℂ)) *
        (hσ.1.eigenvectorBasis k a * conj (hσ.1.eigenvectorBasis k' a)) := fun a => by ring
  simp only [this, ← Finset.mul_sum, hin]
  split_ifs with h
  · subst h
    rw [mul_one, ← Complex.ofReal_mul, Real.mul_self_sqrt (hσ.eigenvalues_nonneg k)]
  · simp

lemma amp_norm {ι : Type} [Fintype ι] [DecidableEq ι] {σ : Matrix ι ι ℂ} (hσ : σ.PosSemidef)
    (k : ι) : ∑ a, ‖amp hσ k a‖ ^ 2 = hσ.1.eigenvalues k := by
  have h := amp_inner hσ k k
  rw [if_pos rfl] at h
  have : ((∑ a, ‖amp hσ k a‖ ^ 2 : ℝ) : ℂ) = ∑ a, amp hσ k a * conj (amp hσ k a) := by
    push_cast
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  exact_mod_cast this.trans h

lemma vn_amp {ι : Type} [Fintype ι] [DecidableEq ι] {σ : Matrix ι ι ℂ} (hσ : σ.PosSemidef) :
    vnEntropy σ = -∑ k, hσ.1.eigenvalues k * Real.logb 2 (hσ.1.eigenvalues k) := by
  rw [X4ZE.vn_eig hσ.1, Finset.sum_div, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun k _ => nml _

/-- finite mixtures of rank-one terms: entropy ≤ Shannon entropy of the weights. -/
lemma fin_bound {ι T : Type} [Fintype ι] [DecidableEq ι] [Fintype T] [DecidableEq T]
    (φ : T → ι → ℂ) :
    vnEntropy (∑ t, Matrix.of fun a b => φ t a * conj (φ t b)) ≤
      -∑ t, (∑ i, ‖φ t i‖ ^ 2) * Real.logb 2 (∑ i, ‖φ t i‖ ^ 2) := by
  set V : Matrix ι T ℂ := Matrix.of fun i t => φ t i
  have hV : (∑ t, Matrix.of fun a b => φ t a * conj (φ t b)) = V * Vᴴ := by
    ext a b; simp [V, Matrix.mul_apply, Matrix.sum_apply, conjTranspose_apply]
  rw [hV, X4KF.x4_ent_swap]
  have hG : ((Vᴴ * V)ᵀ).PosSemidef := (Matrix.posSemidef_conjTranspose_mul_self V).transpose
  obtain ⟨-, -, h⟩ := X4FN.schur hG 1 (one_mem _)
  refine h.trans (le_of_eq ?_)
  rw [Finset.sum_div, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← nml]
  congr 2
  rw [conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  simp only [Matrix.transpose_apply, Matrix.mul_apply, conjTranspose_apply, V, Matrix.of_apply,
    RCLike.star_def, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

/-- `S(Σ σ_m) ≤ Σ S(σ_m)` for unnormalized PSD terms. -/
theorem subconc {ι M : Type} [Fintype ι] [DecidableEq ι] [Fintype M] [DecidableEq M]
    (σ : M → Matrix ι ι ℂ) (hσ : ∀ m, (σ m).PosSemidef) :
    vnEntropy (∑ m, σ m) ≤ ∑ m, vnEntropy (σ m) := by
  have e : ∑ m, σ m = ∑ t : M × ι, Matrix.of fun a b => amp (hσ t.1) t.2 a * conj (amp (hσ t.1) t.2 b) := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun m _ => amp_decomp (hσ m)
  rw [e]
  refine (fin_bound _).trans (le_of_eq ?_)
  rw [Fintype.sum_prod_type, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [vn_amp (hσ m)]
  simp only [amp_norm]

/-- block-diagonal (classical-quantum) assembly. -/
def blk {ι M : Type} [DecidableEq M] (σ : M → Matrix ι ι ℂ) : Matrix (M × ι) (M × ι) ℂ :=
  fun x y => if x.1 = y.1 then σ x.1 x.2 y.2 else 0

lemma blk_decomp {ι M : Type} [Fintype ι] [DecidableEq ι] [Fintype M] [DecidableEq M]
    (σ : M → Matrix ι ι ℂ) (hσ : ∀ m, (σ m).PosSemidef) :
    blk σ = ∑ t : M × ι, Matrix.of fun x y =>
      (if x.1 = t.1 then amp (hσ t.1) t.2 x.2 else 0) *
        conj (if y.1 = t.1 then amp (hσ t.1) t.2 y.2 else 0) := by
  ext x y
  rw [Matrix.sum_apply, Fintype.sum_prod_type, Finset.sum_eq_single x.1]
  · obtain ⟨x1, x2⟩ := x; obtain ⟨y1, y2⟩ := y
    by_cases h : x1 = y1
    · subst h
      simp only [blk, Matrix.of_apply, if_true]
      conv_lhs => rw [amp_decomp (hσ x1)]
      simp [Matrix.sum_apply]
    · simp [blk, Matrix.of_apply, h, Ne.symm h]
  · intro m _ hm
    refine Finset.sum_eq_zero fun k _ => ?_
    simp [Matrix.of_apply, Ne.symm hm]
  · simp

lemma vn_blk {ι M : Type} [Fintype ι] [DecidableEq ι] [Fintype M] [DecidableEq M]
    (σ : M → Matrix ι ι ℂ) (hσ : ∀ m, (σ m).PosSemidef) :
    vnEntropy (blk σ) = ∑ m, vnEntropy (σ m) := by
  rw [blk_decomp σ hσ, orth_ent]
  · rw [Fintype.sum_prod_type, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [vn_amp (hσ m)]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    have : ∑ x : M × ι, ‖(if x.1 = m then amp (hσ m) k x.2 else 0)‖ ^ 2 =
        (hσ m).1.eigenvalues k := by
      rw [Fintype.sum_prod_type, Finset.sum_eq_single m (fun b _ hb => by simp [hb]) (by simp)]
      simp [amp_norm]
    rw [this]
  · intro t t' htt
    rw [Fintype.sum_prod_type]
    by_cases h1 : t.1 = t'.1
    · rw [Finset.sum_eq_single t.1 (fun b _ hb => by simp [hb]) (by simp)]
      simp only [if_true, ← h1]
      rw [amp_inner, if_neg]
      intro h2; exact htt (Prod.ext h1 h2)
    · refine Finset.sum_eq_zero fun m _ => Finset.sum_eq_zero fun a _ => ?_
      by_cases hm : m = t.1
      · subst hm; simp [Ne.symm h1, h1]
      · simp [hm]

/-- concavity: `Σ (S(σ_m) + p_m log p_m) ≤ S(Σ σ_m)` with `p_m = tr σ_m`, `Σ p_m = 1`. -/
theorem conc {ι M : Type} [Fintype ι] [DecidableEq ι] [Fintype M] [DecidableEq M]
    (σ : M → Matrix ι ι ℂ) (hσ : ∀ m, (σ m).PosSemidef) (h1 : ∑ m, (σ m).trace = 1) :
    ∑ m, (vnEntropy (σ m) + (σ m).trace.re * Real.logb 2 (σ m).trace.re) ≤
      vnEntropy (∑ m, σ m) := by
  have hpsd : (blk σ).PosSemidef := by
    rw [blk_decomp σ hσ]
    refine Matrix.posSemidef_sum _ fun t _ => ?_
    have := Matrix.posSemidef_vecMulVec_self_star (fun x : M × ι =>
      if x.1 = t.1 then amp (hσ t.1) t.2 x.2 else 0)
    convert this using 1
    ext x y; simp [vecMulVec_apply]
  have htr : (blk σ).trace = 1 := by
    rw [← h1, Matrix.trace, Fintype.sum_prod_type]
    simp [blk, Matrix.trace]
  have hsub := X4SU.subadd (blk σ) hpsd htr
  have hR : traceRight (blk σ) = diagonal fun m => (((σ m).trace.re : ℝ) : ℂ) := by
    ext m m'
    simp only [traceRight, Matrix.of_apply, blk, diagonal_apply]
    split_ifs with h
    · subst h
      have hn := Complex.nonneg_iff.1 (hσ m).trace_nonneg
      have hre : (((σ m).trace.re : ℝ) : ℂ) = (σ m).trace :=
        Complex.ext (by simp) (by simp [hn.2])
      rw [hre]; rfl
    · simp
  have hL : traceLeft (blk σ) = ∑ m, σ m := by
    ext a b; simp [traceLeft, blk, Matrix.sum_apply]
  rw [hR, hL, vn_diag, vn_blk σ hσ] at hsub
  rw [Finset.sum_add_distrib]
  linarith

end X4LE

end

-- ===== LEB =====

/-! Kraus branches of a bipartite pure vector: Bob marginals, the unnormalized entanglement
functional `Gv` and its monotonicity under Alice-side Kraus families. -/

noncomputable section

namespace X4LE
open Matrix Real QAlgorithms
open QAlgorithms.Papers.Independent.Support50.P42
open QAlgorithms.Papers.Independent.Next46.P39 (rectAct)
open scoped Matrix ComplexConjugate ComplexOrder

variable {a b : ℕ}

/-- reshaped coefficient matrix. -/
def Mv {α β : Type} (v : EuclideanSpace ℂ (α × β)) : Matrix α β ℂ := Matrix.of fun x y => v (x, y)

lemma akb_apply {c : ℕ} (A : Matrix (Fin c) (Fin a) ℂ) (ψ : EuclideanSpace ℂ (Fin a × Fin b))
    (x : Fin c × Fin b) : aliceKetBranch A ψ x = ∑ τ, A x.1 τ * ψ (τ, x.2) := by
  unfold aliceKetBranch rectAct
  simp only [PiLp.toLp_apply, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply, Matrix.kronecker, Matrix.one_apply]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.sum_eq_single x.2]
  · simp
  · intro β _ hβ; simp [Ne.symm hβ]
  · simp

lemma Mv_akb {c : ℕ} (A : Matrix (Fin c) (Fin a) ℂ) (ψ : EuclideanSpace ℂ (Fin a × Fin b)) :
    Mv (aliceKetBranch A ψ) = A * Mv ψ := by
  ext x y; simp [Mv, akb_apply, Matrix.mul_apply]

lemma tl_eq {α β : Type} [Fintype α] [Fintype β] (v : EuclideanSpace ℂ (α × β)) :
    traceLeft (pureDensity v) = ((Mv v)ᴴ * Mv v)ᵀ := by
  ext y y'
  simp [traceLeft, pureDensity, Mv, Matrix.mul_apply, mul_comm]

lemma tr_eq {α β : Type} [Fintype α] [Fintype β] (v : EuclideanSpace ℂ (α × β)) :
    traceRight (pureDensity v) = Mv v * (Mv v)ᴴ := by
  ext y y'
  simp [traceRight, pureDensity, Mv, Matrix.mul_apply]

lemma tl_psd {α β : Type} [Fintype α] [Fintype β] (v : EuclideanSpace ℂ (α × β)) :
    (traceLeft (pureDensity v)).PosSemidef := by
  rw [tl_eq]; exact (posSemidef_conjTranspose_mul_self _).transpose

lemma tl_trace {α β : Type} [Fintype α] [Fintype β] (v : EuclideanSpace ℂ (α × β)) :
    (traceLeft (pureDensity v)).trace = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
  rw [EuclideanSpace.norm_sq_eq]
  push_cast
  simp only [Matrix.trace, traceLeft, pureDensity, Matrix.diag, Matrix.of_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl

lemma tl_trace_re {α β : Type} [Fintype α] [Fintype β] (v : EuclideanSpace ℂ (α × β)) :
    (traceLeft (pureDensity v)).trace.re = ‖v‖ ^ 2 := by
  rw [tl_trace]; exact_mod_cast Complex.ofReal_re _

lemma vn_zero {ι : Type*} [Fintype ι] [DecidableEq ι] : vnEntropy (0 : Matrix ι ι ℂ) = 0 := by
  unfold vnEntropy; simp

lemma tl_smul {α β : Type} [Fintype α] (c : ℂ) (M : Matrix (α × β) (α × β) ℂ) :
    traceLeft (c • M) = c • traceLeft M := by
  ext; simp [traceLeft, Finset.mul_sum]

lemma pd_smul {α : Type} (c : ℂ) (v : EuclideanSpace ℂ α) :
    pureDensity (c • v) = ((‖c‖ ^ 2 : ℝ) : ℂ) • pureDensity v := by
  ext x y
  simp only [pureDensity, Matrix.of_apply, Matrix.smul_apply, PiLp.smul_apply, smul_eq_mul, map_mul]
  have : c * conj c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [← this]; ring

/-- Kraus completeness: the Bob marginal is unchanged on average. -/
lemma tl_sum {M : Type} [Fintype M] (c : M → ℕ) (A : ∀ m, Matrix (Fin (c m)) (Fin a) ℂ)
    (hA : ∑ m, (A m)ᴴ * A m = 1) (ψ : EuclideanSpace ℂ (Fin a × Fin b)) :
    ∑ m, traceLeft (pureDensity (aliceKetBranch (A m) ψ)) = traceLeft (pureDensity ψ) := by
  simp only [tl_eq, Mv_akb, conjTranspose_mul]
  rw [← Matrix.transpose_sum]
  congr 1
  have : ∀ m, (Mv ψ)ᴴ * (A m)ᴴ * (A m * Mv ψ) = (Mv ψ)ᴴ * ((A m)ᴴ * A m) * Mv ψ := fun m => by
    simp only [Matrix.mul_assoc]
  simp only [this]
  rw [← Matrix.sum_mul, ← Matrix.mul_sum, hA, Matrix.mul_one]

lemma akb_smul {c : ℕ} (A : Matrix (Fin c) (Fin a) ℂ) (z : ℂ) (ψ : EuclideanSpace ℂ (Fin a × Fin b)) :
    aliceKetBranch A (z • ψ) = z • aliceKetBranch A ψ := by
  ext x; simp only [akb_apply, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- unnormalized entanglement functional: `‖v‖² · S(Bob marginal of v/‖v‖)`. -/
def Gv {α β : Type} [Fintype α] [Fintype β] [DecidableEq β] (v : EuclideanSpace ℂ (α × β)) : ℝ :=
  vnEntropy (traceLeft (pureDensity v)) + ‖v‖ ^ 2 * Real.logb 2 (‖v‖ ^ 2)

lemma Gv_zero {α β : Type} [Fintype α] [Fintype β] [DecidableEq β] :
    Gv (0 : EuclideanSpace ℂ (α × β)) = 0 := by
  have : pureDensity (0 : EuclideanSpace ℂ (α × β)) = 0 := by ext; simp [pureDensity]
  have h2 : traceLeft (0 : Matrix (α × β) (α × β) ℂ) = 0 := by ext; simp [traceLeft]
  simp [Gv, this, h2, vn_zero]

lemma Gv_smul {α β : Type} [Fintype α] [Fintype β] [DecidableEq β] (z : ℂ)
    (v : EuclideanSpace ℂ (α × β)) : Gv (z • v) = ‖z‖ ^ 2 * Gv v := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [Gv_zero]
  rcases eq_or_ne v 0 with rfl | hv
  · simp [Gv_zero]
  have hz2 : 0 < ‖z‖ ^ 2 := by positivity
  have hv2 : 0 < ‖v‖ ^ 2 := by have := norm_pos_iff.2 hv; positivity
  unfold Gv
  rw [pd_smul, tl_smul, vn_smul (tl_psd v).1 hz2, tl_trace_re, norm_smul, mul_pow,
    Real.logb_mul hz2.ne' hv2.ne']
  ring

lemma Gv_unit {α β : Type} [Fintype α] [Fintype β] [DecidableEq β] (v : EuclideanSpace ℂ (α × β))
    (hv : ‖v‖ = 1) : Gv v = vnEntropy (traceLeft (pureDensity v)) := by
  simp [Gv, hv]

lemma Gv_branch {α β : Type} [Fintype α] [Fintype β] [DecidableEq β] (v : EuclideanSpace ℂ (α × β)) :
    Gv v = vnEntropy (traceLeft (pureDensity v)) +
      (traceLeft (pureDensity v)).trace.re * Real.logb 2 (traceLeft (pureDensity v)).trace.re := by
  rw [tl_trace_re]; rfl

/-- monotonicity of `Gv` under any Alice-side Kraus family (outputs may differ). -/
theorem mono {M : Type} [Fintype M] [DecidableEq M] (c : M → ℕ)
    (A : ∀ m, Matrix (Fin (c m)) (Fin a) ℂ) (hA : ∑ m, (A m)ᴴ * A m = 1)
    (ψ : EuclideanSpace ℂ (Fin a × Fin b)) :
    ∑ m, Gv (aliceKetBranch (A m) ψ) ≤ Gv ψ := by
  rcases eq_or_ne ψ 0 with rfl | hψ
  · have : ∀ m, aliceKetBranch (A m) (0 : EuclideanSpace ℂ (Fin a × Fin b)) = 0 := fun m => by
      have := akb_smul (A m) 0 (0 : EuclideanSpace ℂ (Fin a × Fin b)); simpa using this
    simp [this, Gv_zero]
  have hn : 0 < ‖ψ‖ := norm_pos_iff.2 hψ
  set u : EuclideanSpace ℂ (Fin a × Fin b) := ((‖ψ‖⁻¹ : ℝ) : ℂ) • ψ
  have hu : ‖u‖ = 1 := by
    simp only [u, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm]
    field_simp
  have hψu : ψ = ((‖ψ‖ : ℝ) : ℂ) • u := by
    simp only [u, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hn.ne', Complex.ofReal_one,
      one_smul]
  rw [hψu]
  simp only [akb_smul, Gv_smul, ← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [Gv_unit u hu, ← tl_sum c A hA u]
  simp only [Gv_branch]
  refine conc _ (fun m => tl_psd _) ?_
  rw [← Matrix.trace_sum, tl_sum c A hA u, tl_trace, hu]; simp

/-- swap of the two tensor factors. -/
def swapV {α β : Type} (v : EuclideanSpace ℂ (α × β)) : EuclideanSpace ℂ (β × α) :=
  WithLp.toLp 2 fun p => v (p.2, p.1)

lemma norm_swapV {α β : Type} [Fintype α] [Fintype β] (v : EuclideanSpace ℂ (α × β)) :
    ‖swapV v‖ = ‖v‖ := by
  have : ‖swapV v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type,
      Fintype.sum_prod_type, Finset.sum_comm]
    rfl
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this

lemma Gv_swap {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (v : EuclideanSpace ℂ (α × β)) : Gv (swapV v) = Gv v := by
  unfold Gv
  rw [norm_swapV]
  congr 1
  have e1 : traceLeft (pureDensity (swapV v)) = Mv v * (Mv v)ᴴ := by
    ext; simp [traceLeft, pureDensity, swapV, Mv, Matrix.mul_apply]
  rw [e1, X4KF.x4_ent_swap, tl_eq]

end X4LE

end

-- ===== ZEB =====

noncomputable section

namespace X4ZE
open Matrix QAlgorithms Real
open QAlgorithms.Papers.Independent.Support50.P42
open QAlgorithms.Papers.Independent.Claimed50.P33
open QAlgorithms.Papers.Independent.Gap48.P32 (pairOfState)
open scoped Matrix ComplexConjugate ComplexOrder

/-- separable (sum of product pure terms), stated through zero-extended entries. -/
def Sep (s : Shared) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (f g : ι → ℕ → ℂ), ∀ x y : Fin 2 → ℕ,
    (∀ i, x i < s.dims i) → (∀ i, y i < s.dims i) →
      stateEntry s x y = ∑ k, f k (x 0) * g k (x 1) * conj (f k (y 0) * g k (y 1))

lemma se_in (s : Shared) (x y : Fin 2 → ℕ) (hx : ∀ i, x i < s.dims i) (hy : ∀ i, y i < s.dims i) :
    stateEntry s x y = s.rho (fun i => ⟨x i, hx i⟩) (fun i => ⟨y i, hy i⟩) := by
  unfold stateEntry; rw [dif_pos ⟨hx, hy⟩]

lemma rho_se (s : Shared) (a b : RegisterBasis (fun i => Fin (s.dims i))) :
    s.rho a b = stateEntry s (fun i => (a i).val) (fun i => (b i).val) := by
  rw [se_in s _ _ (fun i => (a i).isLt) (fun i => (b i).isLt)]

lemma rho_of_sep {s : Shared} (hS : Sep s) : ∃ (ι : Type) (_ : Fintype ι) (f g : ι → ℕ → ℂ),
    ∀ a b : RegisterBasis (fun i => Fin (s.dims i)), s.rho a b =
      ∑ k, (f k (a 0).val * g k (a 1).val) * conj (f k (b 0).val * g k (b 1).val) := by
  obtain ⟨ι, _, f, g, h⟩ := hS
  exact ⟨ι, inferInstance, f, g, fun a b => by
    rw [rho_se, h _ _ (fun i => (a i).isLt) (fun i => (b i).isLt)]⟩

lemma sandwich {m n ι : Type*} [Fintype n] [Fintype ι] (L : Matrix m n ℂ) (ρ : Matrix n n ℂ)
    (h : ι → n → ℂ) (hρ : ∀ a b, ρ a b = ∑ k, h k a * conj (h k b)) (X Y : m) :
    (L * ρ * Lᴴ) X Y = ∑ k, (∑ a, L X a * h k a) * conj (∑ b, L Y b * h k b) := by
  simp only [Matrix.mul_apply, conjTranspose_apply, RCLike.star_def, hρ, map_sum, map_mul,
    Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => ?_
  ring

lemma sep_of (t : Shared) (ι : Type) [Fintype ι] (K : ι → RegisterBasis (fun i => Fin (t.dims i)) → ℂ)
    (c : ℝ) (hc : 0 < c) (hK : ∀ X Y, (c : ℂ) * t.rho X Y = ∑ i, K i X * conj (K i Y))
    (F G : ι → ℕ → ℂ) (hFG : ∀ i X, K i X = F i (X 0).val * G i (X 1).val) : Sep t := by
  refine ⟨ι, inferInstance, fun i n => ((Real.sqrt c)⁻¹ : ℝ) * F i n, G, fun x y hx hy => ?_⟩
  rw [se_in t x y hx hy]
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have e := hK (fun i => ⟨x i, hx i⟩) (fun i => ⟨y i, hy i⟩)
  have hs : ((Real.sqrt c)⁻¹ : ℝ) * ((Real.sqrt c)⁻¹ : ℝ) = (c⁻¹ : ℝ) := by
    rw [← mul_inv, Real.mul_self_sqrt hc.le]
  have hsC : ((Real.sqrt c)⁻¹ : ℂ) * ((Real.sqrt c)⁻¹ : ℂ) = (c : ℂ)⁻¹ := by
    exact_mod_cast hs
  calc t.rho (fun i => ⟨x i, hx i⟩) (fun i => ⟨y i, hy i⟩)
      = (c : ℂ)⁻¹ * ((c : ℂ) * t.rho (fun i => ⟨x i, hx i⟩) (fun i => ⟨y i, hy i⟩)) := by
        field_simp
    _ = _ := by
      rw [e, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hFG, hFG]
      push_cast
      simp only [map_mul, map_inv₀, Complex.conj_ofReal]
      rw [← hsC]; ring

lemma sum_pi2 {d : Fin 2 → ℕ} (F : ((i : Fin 2) → Fin (d i)) → ℂ) :
    ∑ a, F a = ∑ q : Fin (d 0) × Fin (d 1), F ((piFinTwoEquiv (fun i => Fin (d i))).symm q) :=
  (Equiv.sum_comp (piFinTwoEquiv (fun i => Fin (d i))).symm F).symm

lemma K0 (s t : Shared) (A : Matrix (Fin (t.dims 0)) (Fin (s.dims 0)) ℂ) (hd1 : t.dims 1 = s.dims 1)
    (f g : ℕ → ℂ) (X : RegisterBasis (fun i => Fin (t.dims i))) :
    ∑ a, liftLocalKraus s t 0 A X a * (f (a 0).val * g (a 1).val) =
      (∑ τ, A (X 0) τ * f τ.val) * g (X 1).val := by
  rw [sum_pi2, Fintype.sum_prod_type, Finset.sum_mul]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hlt : (X 1).val < s.dims 1 := hd1 ▸ (X 1).isLt
  rw [Finset.sum_eq_single ⟨(X 1).val, hlt⟩]
  · simp [liftLocalKraus, Fin.forall_fin_two]; ring
  · intro u _ hu
    have : ¬ ((X 1).val = u.val) := fun h => hu (Fin.ext h.symm)
    simp [liftLocalKraus, Fin.forall_fin_two, this]
  · simp

lemma K1 (s t : Shared) (A : Matrix (Fin (t.dims 1)) (Fin (s.dims 1)) ℂ) (hd0 : t.dims 0 = s.dims 0)
    (f g : ℕ → ℂ) (X : RegisterBasis (fun i => Fin (t.dims i))) :
    ∑ a, liftLocalKraus s t 1 A X a * (f (a 0).val * g (a 1).val) =
      f (X 0).val * ∑ τ, A (X 1) τ * g τ.val := by
  rw [sum_pi2, Fintype.sum_prod_type]
  have hlt : (X 0).val < s.dims 0 := hd0 ▸ (X 0).isLt
  rw [Finset.sum_eq_single ⟨(X 0).val, hlt⟩]
  · simp [liftLocalKraus, Fin.forall_fin_two, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    ring
  · intro u _ hu
    have : ¬ ((X 0).val = u.val) := fun h => hu (Fin.ext h.symm)
    simp [liftLocalKraus, Fin.forall_fin_two, this]
  · simp

lemma sep_step {s : Shared} {k : ℕ} {p : Fin k → ℝ} {r : Fin k → Shared} (h : LocalInstrument s p r)
    (hS : Sep s) (j : Fin k) (hp : 0 < p j) : Sep (r j) := by
  obtain ⟨_, _, party, count, A, hd, _, hsub⟩ := h
  obtain ⟨ι, _, f, g, hρ⟩ := rho_of_sep hS
  have hK : ∀ X Y, ((p j : ℝ) : ℂ) * (r j).rho X Y = ∑ i : Fin (count j) × ι,
      (∑ a, liftLocalKraus s (r j) party (A j i.1) X a * (f i.2 (a 0).val * g i.2 (a 1).val)) *
      conj (∑ b, liftLocalKraus s (r j) party (A j i.1) Y b * (f i.2 (b 0).val * g i.2 (b 1).val)) := by
    intro X Y
    have e := congrFun (congrFun (hsub j) X) Y
    rw [Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply] at e
    rw [e, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun z _ => ?_
    exact sandwich (liftLocalKraus s (r j) party (A j z)) s.rho
      (fun i a => f i (a 0).val * g i (a 1).val) hρ X Y
  obtain rfl | rfl : party = 0 ∨ party = 1 := by fin_cases party <;> simp
  · refine sep_of (r j) _ _ (p j) hp hK
      (fun i n => if h : n < (r j).dims 0 then ∑ τ, A j i.1 ⟨n, h⟩ τ * f i.2 τ.val else 0)
      (fun i n => g i.2 n) fun i X => ?_
    rw [K0 s (r j) _ (hd j 1 (by decide)), dif_pos (X 0).isLt]
  · refine sep_of (r j) _ _ (p j) hp hK (fun i n => f i.2 n)
      (fun i n => if h : n < (r j).dims 1 then ∑ τ, A j i.1 ⟨n, h⟩ τ * g i.2 τ.val else 0)
      fun i X => ?_
    rw [K1 s (r j) _ (hd j 0 (by decide)), dif_pos (X 1).isLt]

lemma sep_list (d : Fin 2 → ℕ) (l : List (ℝ × Shared)) (hd : ∀ w ∈ l, w.2.dims = d)
    (h0 : ∀ w ∈ l, 0 ≤ w.1) (hS : ∀ w ∈ l, 0 < w.1 → Sep w.2) :
    ∃ (ι : Type) (_ : Fintype ι) (f g : ι → ℕ → ℂ), ∀ x y : Fin 2 → ℕ,
      (∀ i, x i < d i) → (∀ i, y i < d i) →
        (l.map fun w => (w.1 : ℂ) * stateEntry w.2 x y).sum =
          ∑ k, f k (x 0) * g k (x 1) * conj (f k (y 0) * g k (y 1)) := by
  induction l with
  | nil => exact ⟨Empty, inferInstance, fun e => e.elim, fun e => e.elim, fun x y _ _ => by simp⟩
  | cons w l ih =>
    obtain ⟨ι, _, f, g, hl⟩ := ih (fun v hv => hd v (List.mem_cons_of_mem _ hv))
      (fun v hv => h0 v (List.mem_cons_of_mem _ hv)) (fun v hv => hS v (List.mem_cons_of_mem _ hv))
    rcases (h0 w List.mem_cons_self).eq_or_lt with hw | hw
    · refine ⟨ι, inferInstance, f, g, fun x y hx hy => ?_⟩
      rw [List.map_cons, List.sum_cons, ← hw, hl x y hx hy]; simp
    obtain ⟨κ, _, f1, g1, h1⟩ := hS w List.mem_cons_self hw
    have hdw := hd w List.mem_cons_self
    refine ⟨κ ⊕ ι, inferInstance, Sum.elim (fun k n => ((Real.sqrt w.1 : ℝ) : ℂ) * f1 k n) f,
      Sum.elim g1 g, fun x y hx hy => ?_⟩
    rw [List.map_cons, List.sum_cons, hl x y hx hy, Fintype.sum_sum_type,
      h1 x y (fun i => hdw ▸ hx i) (fun i => hdw ▸ hy i), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    have hs : ((Real.sqrt w.1 : ℝ) : ℂ) * ((Real.sqrt w.1 : ℝ) : ℂ) = (w.1 : ℂ) := by
      exact_mod_cast Real.mul_self_sqrt hw.le
    simp only [Sum.elim_inl, map_mul, Complex.conj_ofReal]
    rw [← hs]; ring

lemma main {s : Shared} {out : List (ℝ × Shared)} (h : LocalTree s out) :
    (∀ w ∈ out, 0 ≤ w.1) ∧ (Sep s → ∀ w ∈ out, 0 < w.1 → Sep w.2) := by
  induction h with
  | stop s => exact ⟨fun w hw => by simp at hw; simp [hw], fun hS w hw _ => by simp at hw; simp [hw, hS]⟩
  | step s k p r hI next hn ih =>
    have hp0 := hI.1
    refine ⟨fun w hw => ?_, fun hS w hw hpos => ?_⟩
    · simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_map] at hw
      obtain ⟨j, v, hv, rfl⟩ := hw
      exact mul_nonneg (hp0 j) ((ih j).1 v hv)
    · simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_map] at hw
      obtain ⟨j, v, hv, rfl⟩ := hw
      have hv0 := (ih j).1 v hv
      have hpj : 0 < p j := by
        rcases (hp0 j).eq_or_lt with e | e
        · simp [← e] at hpos
        · exact e
      have hvp : 0 < v.1 := by
        rcases hv0.eq_or_lt with e | e
        · simp [← e] at hpos
        · exact e
      exact (ih j).2 (sep_step hI hS j hpj) v hv hvp
  | forget s t out hl hd hmix ih =>
    refine ⟨fun w hw => by simp at hw; simp [hw], fun hS w hw _ => ?_⟩
    simp at hw; subst hw
    obtain ⟨ι, _, f, g, hfg⟩ := sep_list t.dims out hd ih.1 (ih.2 hS)
    exact ⟨ι, inferInstance, f, g, fun x y hx hy => by rw [hmix, hfg x y hx hy]⟩

end X4ZE

end

-- ===== ZEC =====

noncomputable section

namespace X4ZE
open Matrix QAlgorithms Real
open QAlgorithms.Papers.Independent.Support50.P42
open QAlgorithms.Papers.Independent.Claimed50.P33
open QAlgorithms.Papers.Independent.Gap48.P32 (pairOfState)
open scoped Matrix ComplexConjugate ComplexOrder

lemma spec_of {ι : Type*} [Fintype ι] [DecidableEq ι] {X : Matrix ι ι ℂ} (hX : X.IsHermitian) {c : ℝ}
    (h : X * X = (c : ℂ) • X) : ∀ x ∈ spectrum ℝ X, x = 0 ∨ x = c := by
  have hsa : IsSelfAdjoint X := hX
  have e : cfc (fun x : ℝ => x * x) X = cfc (fun x : ℝ => c * x) X := by
    rw [cfc_mul (fun x : ℝ => x) (fun x : ℝ => x) X, cfc_id' ℝ X, cfc_const_mul_id c X, h]
    rw [Complex.coe_smul]
  intro x hx
  have := (eqOn_of_cfc_eq_cfc e : Set.EqOn _ _ _) hx
  simp only at this
  have : x * (x - c) = 0 := by linarith
  rcases mul_eq_zero.1 this with h0 | h0
  · exact Or.inl h0
  · exact Or.inr (by linarith)

lemma vn_scaled {ι : Type*} [Fintype ι] [DecidableEq ι] {X : Matrix ι ι ℂ} (hX : X.IsHermitian) {c : ℝ}
    (h : X * X = (c : ℂ) • X) : vnEntropy X = -(Real.logb 2 c * X.trace.re) := by
  unfold vnEntropy
  have hsa : IsSelfAdjoint X := hX
  rw [cfc_congr (g := fun x : ℝ => Real.logb 2 c * x)]
  · rw [cfc_const_mul_id _ X, Matrix.trace_smul, Complex.real_smul, Complex.re_ofReal_mul]
  · intro x hx
    rcases spec_of hX h x hx with rfl | rfl
    · simp
    · ring

lemma tl_psd {α β : Type*} [Fintype α] [Fintype β] (v : EuclideanSpace ℂ (α × β)) (hv : ‖v‖ = 1) :
    (traceLeft (pureDensity v)).PosSemidef ∧ (traceLeft (pureDensity v)).trace = 1 := by
  set W : Matrix β α ℂ := Matrix.of fun b a => v (a, b)
  have hW : traceLeft (pureDensity v) = W * Wᴴ := by
    ext b b'
    simp [traceLeft, pureDensity, W, Matrix.mul_apply, conjTranspose_apply]
  refine ⟨hW ▸ posSemidef_self_mul_conjTranspose W, ?_⟩
  rw [← unit_sum v hv, Fintype.sum_prod_type, Finset.sum_comm]
  simp [Matrix.trace, traceLeft, pureDensity]

lemma rho_pair (s : Shared) (X Y : RegisterBasis (fun i => Fin (s.dims i))) :
    s.rho X Y = pairOfState s (X 0, X 1) (Y 0, Y 1) := by
  unfold pairOfState
  congr 1 <;> funext i <;> fin_cases i <;> rfl

lemma sep_init (s : Shared) (hs : IsPureShared s) (hz : ent s = 0) : Sep s := by
  obtain ⟨v, hv1, hv⟩ := hs
  have hent : vnEntropy (traceLeft (pureDensity v)) = 0 := by
    have : ent s = vnEntropy (traceLeft (pairOfState s)) := rfl
    rw [this, hv] at hz; exact hz
  obtain ⟨hpsd, htr⟩ := tl_psd v hv1
  obtain ⟨w, hw1, hw⟩ := pure_of_vn hpsd htr hent
  have hsplit := rank1_split (fun b => w b) (unit_sum w hw1) (fun a b => v (a, b)) (fun b b' => by
    have := congrFun (congrFun hw b) b'
    simp only [traceLeft, pureDensity, Matrix.of_apply] at this
    exact this.symm)
  refine ⟨Unit, inferInstance,
    fun _ n => if h : n < s.dims 0 then ∑ b, conj (w b) * v (⟨n, h⟩, b) else 0,
    fun _ n => if h : n < s.dims 1 then w ⟨n, h⟩ else 0, fun x y hx hy => ?_⟩
  rw [se_in s x y hx hy, rho_pair, hv]
  simp only [pureDensity, Matrix.of_apply, Fintype.sum_unique, dif_pos (hx 0), dif_pos (hx 1),
    dif_pos (hy 0), dif_pos (hy 1)]
  rw [hsplit, hsplit (k := ⟨y 0, hy 0⟩)]

lemma ent_of_sep (w : Shared) (hp : IsPureShared w) (hS : Sep w) : ent w = 0 := by
  obtain ⟨v, hv1, hv⟩ := hp
  obtain ⟨ι, _, f, g, hfg⟩ := hS
  set φ : ι → Fin (w.dims 0) × Fin (w.dims 1) → ℂ := fun k a => f k a.1.val * g k a.2.val
  have pk : ∀ a : Fin (w.dims 0) × Fin (w.dims 1), ∀ i, (![a.1.val, a.2.val] : Fin 2 → ℕ) i < w.dims i := by
    intro a i; fin_cases i
    · exact a.1.isLt
    · exact a.2.isLt
  have h : ∀ a b, v a * conj (v b) = ∑ k, φ k a * conj (φ k b) := by
    intro a b
    have e1 : v a * conj (v b) = pairOfState w a b := by rw [hv]; rfl
    have e2 : pairOfState w a b = stateEntry w ![a.1.val, a.2.val] ![b.1.val, b.2.val] := by
      rw [se_in w _ _ (pk a) (pk b), rho_pair]; rfl
    rw [e1, e2, hfg _ _ (pk a) (pk b)]
    rfl
  have hU := unit_sum v hv1
  have hsplit := rank1_split v hU φ h
  set c : ι → ℂ := fun k => ∑ b, conj (v b) * φ k b
  obtain ⟨k0, hk0⟩ : ∃ k, c k ≠ 0 := by
    by_contra hc
    push Not at hc
    have : ∀ a, v a * conj (v a) = 0 := fun a => by
      rw [h]; exact Finset.sum_eq_zero fun k _ => by rw [hsplit k a]; simp [c, hc k]
    rw [Finset.sum_eq_zero fun a _ => this a] at hU
    exact zero_ne_one hU
  set F : Fin (w.dims 0) → ℂ := fun a => (c k0)⁻¹ * f k0 a.val
  set G : Fin (w.dims 1) → ℂ := fun b => g k0 b.val
  have hvFG : ∀ a b, v (a, b) = F a * G b := by
    intro a b
    have := hsplit k0 (a, b)
    simp only [F, G]
    rw [show v (a, b) = (c k0)⁻¹ * φ k0 (a, b) by rw [this]; field_simp; rfl]
    simp only [φ]; ring
  set N := ∑ a, F a * conj (F a)
  set M := ∑ b, G b * conj (G b)
  have hNM : N * M = 1 := by
    rw [← hU, Fintype.sum_prod_type, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hvFG]; simp only [map_mul]; ring
  set B := traceLeft (pureDensity v)
  have hB : ∀ b b', B b b' = N * (G b * conj (G b')) := by
    intro b b'
    simp only [B, traceLeft, pureDensity, Matrix.of_apply, hvFG, map_mul, N, Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => by ring
  have hBB : B * B = ((1 : ℝ) : ℂ) • B := by
    ext b b''
    rw [Matrix.mul_apply, Complex.ofReal_one, one_smul]
    simp only [hB]
    calc ∑ b', N * (G b * conj (G b')) * (N * (G b' * conj (G b'')))
        = N * (N * M) * (G b * conj (G b'')) := by
          simp only [M, Finset.mul_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun b' _ => by ring
      _ = _ := by rw [hNM, mul_one]
  have hent := vn_scaled (tl_psd v hv1).1.1 hBB
  have : ent w = vnEntropy B := by
    show vnEntropy (traceLeft (pairOfState w)) = _
    rw [hv]
  rw [this, hent]; simp

end X4ZE

end

-- ===== LEC =====

/-! Convex-roof invariant for `Claimed50.P33.LOCC` trees: the pure-decomposition infimum `E`
(entanglement of formation in unnormalized form) never increases on average. -/

noncomputable section

namespace X4LE
open Matrix Real QAlgorithms
open QAlgorithms.Papers.Independent.Support50.P42
open QAlgorithms.Papers.Independent.Claimed50.P33
open QAlgorithms.Papers.Independent.Gap48.P32 (pairOfState)
open scoped Matrix ComplexConjugate ComplexOrder

def vecN (a b : ℕ) (f : ℕ × ℕ → ℂ) : EuclideanSpace ℂ (Fin a × Fin b) :=
  WithLp.toLp 2 fun p => f (p.1.val, p.2.val)

def Gn (a b : ℕ) (f : ℕ × ℕ → ℂ) : ℝ := Gv (vecN a b f)

def aliceN {c a : ℕ} (A : Matrix (Fin c) (Fin a) ℂ) (f : ℕ × ℕ → ℂ) : ℕ × ℕ → ℂ :=
  fun n => if h : n.1 < c then ∑ τ, A ⟨n.1, h⟩ τ * f (τ.val, n.2) else 0

def bobN {c b : ℕ} (A : Matrix (Fin c) (Fin b) ℂ) (f : ℕ × ℕ → ℂ) : ℕ × ℕ → ℂ :=
  fun n => if h : n.2 < c then ∑ τ, A ⟨n.2, h⟩ τ * f (n.1, τ.val) else 0

def swN (f : ℕ × ℕ → ℂ) : ℕ × ℕ → ℂ := fun n => f (n.2, n.1)

lemma vecN_alice {a b c : ℕ} (A : Matrix (Fin c) (Fin a) ℂ) (f : ℕ × ℕ → ℂ) :
    vecN c b (aliceN A f) = aliceKetBranch A (vecN a b f) := by
  ext x
  simp [vecN, aliceN, akb_apply]

lemma swN_bobN {c b : ℕ} (A : Matrix (Fin c) (Fin b) ℂ) (f : ℕ × ℕ → ℂ) :
    swN (bobN A f) = aliceN A (swN f) := rfl

lemma Gn_swap (a b : ℕ) (f : ℕ × ℕ → ℂ) : Gn a b f = Gn b a (swN f) := by
  unfold Gn
  have : vecN b a (swN f) = swapV (vecN a b f) := rfl
  rw [this, Gv_swap]

lemma Gn_smul (a b : ℕ) (z : ℂ) (f : ℕ × ℕ → ℂ) :
    Gn a b (fun n => z * f n) = ‖z‖ ^ 2 * Gn a b f := by
  unfold Gn
  have : vecN a b (fun n => z * f n) = z • vecN a b f := by ext; simp [vecN]
  rw [this, Gv_smul]

lemma Gv_nonneg {α β : Type} [Fintype α] [Fintype β] [DecidableEq β] (v : EuclideanSpace ℂ (α × β)) :
    0 ≤ Gv v := by
  rcases eq_or_ne v 0 with rfl | hv
  · rw [Gv_zero]
  have hn : 0 < ‖v‖ := norm_pos_iff.2 hv
  set u : EuclideanSpace ℂ (α × β) := ((‖v‖⁻¹ : ℝ) : ℂ) • v
  have hu : ‖u‖ = 1 := by
    simp only [u, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm]
    field_simp
  have hvu : v = ((‖v‖ : ℝ) : ℂ) • u := by
    simp only [u, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hn.ne', Complex.ofReal_one,
      one_smul]
  rw [hvu, Gv_smul, Gv_unit u hu]
  refine mul_nonneg (by positivity) (X4FN.vn_nonneg (tl_psd u) ?_)
  rw [tl_trace, hu]; simp

lemma Gn_nonneg (a b : ℕ) (f : ℕ × ℕ → ℂ) : 0 ≤ Gn a b f := Gv_nonneg _

/-- pure-state decompositions of a shared state, with their `Gn` value. -/
def Dec (t : Shared) (val : ℝ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (f : ι → ℕ × ℕ → ℂ),
    (∀ x y : Fin 2 → ℕ, (∀ i, x i < t.dims i) → (∀ i, y i < t.dims i) →
      stateEntry t x y = ∑ k, f k (x 0, x 1) * conj (f k (y 0, y 1))) ∧
    val = ∑ k, Gn (t.dims 0) (t.dims 1) (f k)

/-- convex roof. -/
def E (t : Shared) : ℝ := sInf {v | Dec t v}

lemma Dec_nonneg {t : Shared} {v : ℝ} (h : Dec t v) : 0 ≤ v := by
  obtain ⟨ι, _, f, -, rfl⟩ := h
  exact Finset.sum_nonneg fun k _ => Gn_nonneg _ _ _

lemma pt_eq (t : Shared) (x : Fin 2 → ℕ) (hx : ∀ i, x i < t.dims i) :
    (fun i => (⟨x i, hx i⟩ : Fin (t.dims i))) =
      (piFinTwoEquiv (fun i => Fin (t.dims i))).symm (⟨x 0, hx 0⟩, ⟨x 1, hx 1⟩) := by
  funext i; fin_cases i <;> rfl

lemma Dec_exists (t : Shared) : ∃ v, Dec t v := by
  classical
  have hρ := t.normalized.1
  set e := (piFinTwoEquiv (fun i => Fin (t.dims i))).symm
  refine ⟨_, RegisterBasis (fun i => Fin (t.dims i)), inferInstance,
    fun k n => if h : n.1 < t.dims 0 ∧ n.2 < t.dims 1 then amp hρ k (e (⟨n.1, h.1⟩, ⟨n.2, h.2⟩))
      else 0, fun x y hx hy => ?_, rfl⟩
  rw [X4ZE.se_in t x y hx hy]
  beta_reduce
  simp only [dif_pos (show x 0 < t.dims 0 ∧ x 1 < t.dims 1 from ⟨hx 0, hx 1⟩),
    dif_pos (show y 0 < t.dims 0 ∧ y 1 < t.dims 1 from ⟨hy 0, hy 1⟩)]
  conv_lhs => rw [amp_decomp hρ]
  rw [Matrix.sum_apply]
  simp only [Matrix.of_apply]
  rw [pt_eq t x hx, pt_eq t y hy]

lemma E_le {t : Shared} {v : ℝ} (h : Dec t v) : E t ≤ v :=
  csInf_le ⟨0, fun _ hw => Dec_nonneg hw⟩ h

lemma le_E {t : Shared} {c : ℝ} (h : ∀ v, Dec t v → c ≤ v) : c ≤ E t :=
  le_csInf (Dec_exists t) h

lemma exists_near (t : Shared) {ε : ℝ} (hε : 0 < ε) : ∃ v, Dec t v ∧ v < E t + ε := by
  obtain ⟨v, hv, hlt⟩ := exists_lt_of_csInf_lt (Dec_exists t) (lt_add_of_pos_right (E t) hε)
  exact ⟨v, hv, hlt⟩

/-! ### leaves -/

lemma dec_pure {t : Shared} (hp : IsPureShared t) {v : ℝ} (hD : Dec t v) : v = ent t := by
  obtain ⟨ψ, hψ1, hψ⟩ := hp
  obtain ⟨ι, _, f, hf, rfl⟩ := hD
  set φ : ι → Fin (t.dims 0) × Fin (t.dims 1) → ℂ := fun k p => f k (p.1.val, p.2.val)
  have pk : ∀ p : Fin (t.dims 0) × Fin (t.dims 1), ∀ i,
      (![p.1.val, p.2.val] : Fin 2 → ℕ) i < t.dims i := by
    intro p i; fin_cases i
    · exact p.1.isLt
    · exact p.2.isLt
  have h : ∀ p q, ψ p * conj (ψ q) = ∑ k, φ k p * conj (φ k q) := by
    intro p q
    have e1 : ψ p * conj (ψ q) = pairOfState t p q := by rw [hψ]; rfl
    have e2 : pairOfState t p q = stateEntry t ![p.1.val, p.2.val] ![q.1.val, q.2.val] := by
      rw [X4ZE.se_in t _ _ (pk p) (pk q), X4ZE.rho_pair]; rfl
    rw [e1, e2, hf _ _ (pk p) (pk q)]
    rfl
  have hU := X4ZE.unit_sum ψ hψ1
  have hsplit := X4ZE.rank1_split ψ hU φ h
  set c : ι → ℂ := fun k => ∑ b, conj (ψ b) * φ k b
  have hvec : ∀ k, vecN (t.dims 0) (t.dims 1) (f k) = c k • ψ := by
    intro k; ext p
    simp only [vecN, PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul]
    exact hsplit k p
  have hc : ∑ k, ‖c k‖ ^ 2 = 1 := by
    have e : ∑ p, ψ p * conj (ψ p) = ∑ k, c k * conj (c k) := by
      calc ∑ p, ψ p * conj (ψ p) = ∑ p, ∑ k, φ k p * conj (φ k p) :=
            Finset.sum_congr rfl fun p _ => h p p
        _ = ∑ k, ∑ p, (c k * ψ p) * conj (c k * ψ p) := by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun p _ => by
              rw [hsplit k p]
        _ = ∑ k, c k * conj (c k) * ∑ p, ψ p * conj (ψ p) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun p _ => by rw [map_mul]; ring
        _ = _ := by rw [hU]; simp
    rw [hU] at e
    have : ((∑ k, ‖c k‖ ^ 2 : ℝ) : ℂ) = ∑ k, c k * conj (c k) := by
      push_cast
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
    exact_mod_cast this.trans e.symm
  have hent : ent t = Gv ψ := by
    rw [Gv_unit ψ hψ1]
    show vnEntropy (traceLeft (pairOfState t)) = _
    rw [hψ]
  simp only [Gn, hvec, Gv_smul, ← Finset.sum_mul, hc, one_mul, hent]

lemma E_pure {t : Shared} (hp : IsPureShared t) : E t = ent t := by
  obtain ⟨v, hv⟩ := Dec_exists t
  have hs : {v | Dec t v} = {ent t} := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    refine ⟨dec_pure hp, ?_⟩
    rintro rfl
    rw [← dec_pure hp hv]; exact hv
  unfold E; rw [hs, csInf_singleton]

/-! ### local Kraus steps -/

lemma K0g (s t : Shared) (A : Matrix (Fin (t.dims 0)) (Fin (s.dims 0)) ℂ) (hd1 : t.dims 1 = s.dims 1)
    (f : ℕ × ℕ → ℂ) (X : RegisterBasis (fun i => Fin (t.dims i))) :
    ∑ a, liftLocalKraus s t 0 A X a * f ((a 0).val, (a 1).val) =
      aliceN A f ((X 0).val, (X 1).val) := by
  rw [X4ZE.sum_pi2, Fintype.sum_prod_type]
  simp only [aliceN, dif_pos (X 0).isLt]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hlt : (X 1).val < s.dims 1 := hd1 ▸ (X 1).isLt
  rw [Finset.sum_eq_single ⟨(X 1).val, hlt⟩]
  · simp [liftLocalKraus, Fin.forall_fin_two]
  · intro u _ hu
    have : ¬ ((X 1).val = u.val) := fun h => hu (Fin.ext h.symm)
    simp [liftLocalKraus, Fin.forall_fin_two, this]
  · simp

lemma K1g (s t : Shared) (A : Matrix (Fin (t.dims 1)) (Fin (s.dims 1)) ℂ) (hd0 : t.dims 0 = s.dims 0)
    (f : ℕ × ℕ → ℂ) (X : RegisterBasis (fun i => Fin (t.dims i))) :
    ∑ a, liftLocalKraus s t 1 A X a * f ((a 0).val, (a 1).val) =
      bobN A f ((X 0).val, (X 1).val) := by
  rw [X4ZE.sum_pi2, Fintype.sum_prod_type]
  simp only [bobN, dif_pos (X 1).isLt]
  have hlt : (X 0).val < s.dims 0 := hd0 ▸ (X 0).isLt
  rw [Finset.sum_eq_single ⟨(X 0).val, hlt⟩]
  · simp [liftLocalKraus, Fin.forall_fin_two]
  · intro u _ hu
    have : ¬ ((X 0).val = u.val) := fun h => hu (Fin.ext h.symm)
    simp [liftLocalKraus, Fin.forall_fin_two, this]
  · simp

lemma kraus0 {M : Type} [Fintype M] (s : Shared) (t : M → Shared)
    (B : ∀ m, Matrix (Fin ((t m).dims 0)) (Fin (s.dims 0)) ℂ) (hd : ∀ m, (t m).dims 1 = s.dims 1)
    (h : ∑ m, (liftLocalKraus s (t m) 0 (B m))ᴴ * liftLocalKraus s (t m) 0 (B m) = 1) :
    ∑ m, (B m)ᴴ * B m = 1 := by
  ext α α'
  set e := (piFinTwoEquiv (fun i => Fin (s.dims i))).symm
  have β0 : Fin (s.dims 1) := ⟨0, s.positive 1⟩
  have H := congrFun (congrFun h (e (α, β0))) (e (α', β0))
  have hY : (e (α, β0) = e (α', β0)) ↔ α = α' := by
    rw [e.injective.eq_iff]; simp
  rw [Matrix.one_apply] at H ⊢
  rw [show (if e (α, β0) = e (α', β0) then (1 : ℂ) else 0) = if α = α' then 1 else 0 by
    simp only [hY]] at H
  rw [← H, Matrix.sum_apply, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [Matrix.mul_apply, conjTranspose_apply]
  rw [X4ZE.sum_pi2, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x0 _ => ?_
  have hlt : β0.val < (t m).dims 1 := (hd m).symm ▸ β0.isLt
  rw [Finset.sum_eq_single ⟨β0.val, hlt⟩]
  · simp [liftLocalKraus, Fin.forall_fin_two, e]
  · intro u _ hu
    have : ¬ (u.val = β0.val) := fun h => hu (Fin.ext h)
    simp [liftLocalKraus, Fin.forall_fin_two, this, e]
  · simp

lemma kraus1 {M : Type} [Fintype M] (s : Shared) (t : M → Shared)
    (B : ∀ m, Matrix (Fin ((t m).dims 1)) (Fin (s.dims 1)) ℂ) (hd : ∀ m, (t m).dims 0 = s.dims 0)
    (h : ∑ m, (liftLocalKraus s (t m) 1 (B m))ᴴ * liftLocalKraus s (t m) 1 (B m) = 1) :
    ∑ m, (B m)ᴴ * B m = 1 := by
  ext β β'
  set e := (piFinTwoEquiv (fun i => Fin (s.dims i))).symm
  have α0 : Fin (s.dims 0) := ⟨0, s.positive 0⟩
  have H := congrFun (congrFun h (e (α0, β))) (e (α0, β'))
  have hY : (e (α0, β) = e (α0, β')) ↔ β = β' := by
    rw [e.injective.eq_iff]; simp
  rw [Matrix.one_apply] at H ⊢
  rw [show (if e (α0, β) = e (α0, β') then (1 : ℂ) else 0) = if β = β' then 1 else 0 by
    simp only [hY]] at H
  rw [← H, Matrix.sum_apply, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [Matrix.mul_apply, conjTranspose_apply]
  have hlt : α0.val < (t m).dims 0 := (hd m).symm ▸ α0.isLt
  rw [X4ZE.sum_pi2, Fintype.sum_prod_type,
    Finset.sum_eq_single (⟨α0.val, hlt⟩ : Fin ((t m).dims 0))]
  · refine Finset.sum_congr rfl fun x1 _ => ?_
    simp [liftLocalKraus, Fin.forall_fin_two, e]
  · intro u _ hu
    have : ¬ (u.val = α0.val) := fun h => hu (Fin.ext h)
    refine Finset.sum_eq_zero fun x1 _ => ?_
    simp [liftLocalKraus, Fin.forall_fin_two, this, e]
  · simp

/-- the common bookkeeping of a local instrument step. -/
lemma step_core {s : Shared} {k : ℕ} {p : Fin k → ℝ} {r : Fin k → Shared} (hp0 : ∀ j, 0 ≤ p j)
    (party : Fin 2) (count : Fin k → ℕ)
    (A : (j : Fin k) → Fin (count j) → Matrix (Fin ((r j).dims party)) (Fin (s.dims party)) ℂ)
    (hsub : ∀ j, (p j : ℂ) • (r j).rho =
      ∑ z, liftLocalKraus s (r j) party (A j z) * s.rho * (liftLocalKraus s (r j) party (A j z))ᴴ)
    {ι : Type} [Fintype ι] (f : ι → ℕ × ℕ → ℂ)
    (hρ : ∀ a b, s.rho a b = ∑ i, f i ((a 0).val, (a 1).val) * conj (f i ((b 0).val, (b 1).val)))
    (op : ∀ j, Fin (count j) → (ℕ × ℕ → ℂ) → (ℕ × ℕ → ℂ))
    (hop : ∀ j z g X, ∑ a, liftLocalKraus s (r j) party (A j z) X a * g ((a 0).val, (a 1).val) =
      op j z g ((X 0).val, (X 1).val))
    (hmono : ∀ i, ∑ j, ∑ z, Gn ((r j).dims 0) ((r j).dims 1) (op j z (f i)) ≤
      Gn (s.dims 0) (s.dims 1) (f i)) :
    ∃ vj : Fin k → ℝ, (∀ j, 0 < p j → Dec (r j) (vj j)) ∧
      ∑ j, p j * vj j ≤ ∑ i, Gn (s.dims 0) (s.dims 1) (f i) := by
  refine ⟨fun j => (p j)⁻¹ * ∑ z, ∑ i, Gn ((r j).dims 0) ((r j).dims 1) (op j z (f i)), ?_, ?_⟩
  · intro j hpj
    refine ⟨Fin (count j) × ι, inferInstance,
      fun zi n => ((Real.sqrt (p j))⁻¹ : ℂ) * op j zi.1 (f zi.2) n, fun x y hx hy => ?_, ?_⟩
    · rw [X4ZE.se_in (r j) x y hx hy]
      have e := congrFun (congrFun (hsub j) (fun i => ⟨x i, hx i⟩)) (fun i => ⟨y i, hy i⟩)
      rw [Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply] at e
      have e2 : ∀ z, (liftLocalKraus s (r j) party (A j z) * s.rho *
          (liftLocalKraus s (r j) party (A j z))ᴴ) (fun i => ⟨x i, hx i⟩) (fun i => ⟨y i, hy i⟩) =
          ∑ i, op j z (f i) (x 0, x 1) * conj (op j z (f i) (y 0, y 1)) := by
        intro z
        rw [X4ZE.sandwich _ s.rho (fun i a => f i ((a 0).val, (a 1).val)) hρ]
        simp only [hop]
      simp only [e2] at e
      have hp' : (p j : ℂ) ≠ 0 := by exact_mod_cast hpj.ne'
      have hs : ((Real.sqrt (p j))⁻¹ : ℂ) * conj ((Real.sqrt (p j))⁻¹ : ℂ) = (p j : ℂ)⁻¹ := by
        rw [map_inv₀, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul,
          Real.mul_self_sqrt (hp0 j)]
      rw [Fintype.sum_prod_type]
      calc (r j).rho (fun i => ⟨x i, hx i⟩) (fun i => ⟨y i, hy i⟩)
          = (p j : ℂ)⁻¹ * ((p j : ℂ) * (r j).rho (fun i => ⟨x i, hx i⟩) (fun i => ⟨y i, hy i⟩)) := by
            field_simp
        _ = _ := by
          rw [e, Finset.mul_sum]
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_mul, ← hs]; ring
    · beta_reduce
      rw [Fintype.sum_prod_type, Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Gn_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
        inv_pow, Real.sq_sqrt (hp0 j)]
  · calc ∑ j, p j * ((p j)⁻¹ * ∑ z, ∑ i, Gn ((r j).dims 0) ((r j).dims 1) (op j z (f i)))
        ≤ ∑ j, ∑ z, ∑ i, Gn ((r j).dims 0) ((r j).dims 1) (op j z (f i)) := by
          refine Finset.sum_le_sum fun j _ => ?_
          have h0 : 0 ≤ ∑ z, ∑ i, Gn ((r j).dims 0) ((r j).dims 1) (op j z (f i)) :=
            Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Gn_nonneg _ _ _
          rcases (hp0 j).eq_or_lt with h | h
          · rw [← h]; simpa using h0
          · rw [← mul_assoc, mul_inv_cancel₀ h.ne', one_mul]
      _ = ∑ i, ∑ j, ∑ z, Gn ((r j).dims 0) ((r j).dims 1) (op j z (f i)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_comm]
      _ ≤ _ := Finset.sum_le_sum fun i _ => hmono i

lemma step_dec {s : Shared} {k : ℕ} {p : Fin k → ℝ} {r : Fin k → Shared} (h : LocalInstrument s p r)
    {val : ℝ} (hD : Dec s val) :
    ∃ vj : Fin k → ℝ, (∀ j, 0 < p j → Dec (r j) (vj j)) ∧ ∑ j, p j * vj j ≤ val := by
  obtain ⟨hp0, -, party, count, A, hd, hK, hsub⟩ := h
  obtain ⟨ι, _, f, hf, rfl⟩ := hD
  have hρ : ∀ a b, s.rho a b = ∑ i, f i ((a 0).val, (a 1).val) * conj (f i ((b 0).val, (b 1).val)) :=
    fun a b => by rw [X4ZE.rho_se, hf _ _ (fun i => (a i).isLt) (fun i => (b i).isLt)]
  have hKs : ∑ m : (Σ j, Fin (count j)), (liftLocalKraus s (r m.1) party (A m.1 m.2))ᴴ *
      liftLocalKraus s (r m.1) party (A m.1 m.2) = 1 := by
    rw [Fintype.sum_sigma]; exact hK
  obtain rfl | rfl : party = 0 ∨ party = 1 := by fin_cases party <;> simp
  · have hA := kraus0 s (fun m : (Σ j, Fin (count j)) => r m.1) (fun m => A m.1 m.2)
      (fun m => hd m.1 1 (by decide)) hKs
    refine step_core hp0 0 count A hsub f hρ (fun j z g => aliceN (A j z) g)
      (fun j z g X => K0g s (r j) (A j z) (hd j 1 (by decide)) g X) fun i => ?_
    have e : ∀ j z, Gn ((r j).dims 0) ((r j).dims 1) (aliceN (A j z) (f i)) =
        Gv (aliceKetBranch (A j z) (vecN (s.dims 0) (s.dims 1) (f i))) := by
      intro j z; rw [hd j 1 (by decide)]; unfold Gn; rw [vecN_alice]
    simp only [e]
    rw [← Fintype.sum_sigma (fun m : (Σ j, Fin (count j)) =>
      Gv (aliceKetBranch (A m.1 m.2) (vecN (s.dims 0) (s.dims 1) (f i))))]
    exact mono (fun m : (Σ j, Fin (count j)) => (r m.1).dims 0) (fun m => A m.1 m.2) hA _
  · have hA := kraus1 s (fun m : (Σ j, Fin (count j)) => r m.1) (fun m => A m.1 m.2)
      (fun m => hd m.1 0 (by decide)) hKs
    refine step_core hp0 1 count A hsub f hρ (fun j z g => bobN (A j z) g)
      (fun j z g X => K1g s (r j) (A j z) (hd j 0 (by decide)) g X) fun i => ?_
    have e : ∀ j z, Gn ((r j).dims 0) ((r j).dims 1) (bobN (A j z) (f i)) =
        Gv (aliceKetBranch (A j z) (vecN (s.dims 1) (s.dims 0) (swN (f i)))) := by
      intro j z; rw [hd j 0 (by decide), Gn_swap, swN_bobN]; unfold Gn; rw [vecN_alice]
    simp only [e]
    rw [← Fintype.sum_sigma (fun m : (Σ j, Fin (count j)) =>
      Gv (aliceKetBranch (A m.1 m.2) (vecN (s.dims 1) (s.dims 0) (swN (f i))))),
      Gn_swap]
    exact mono (fun m : (Σ j, Fin (count j)) => (r m.1).dims 1) (fun m => A m.1 m.2) hA _

/-! ### mixtures (forget) -/

lemma mix (d : Fin 2 → ℕ) (l : List (ℝ × Shared)) (hd : ∀ w ∈ l, w.2.dims = d)
    (h0 : ∀ w ∈ l, 0 ≤ w.1) {ε : ℝ} (hε : 0 < ε) :
    ∃ (ι : Type) (_ : Fintype ι) (f : ι → ℕ × ℕ → ℂ),
      (∀ x y : Fin 2 → ℕ, (∀ i, x i < d i) → (∀ i, y i < d i) →
        (l.map fun w => (w.1 : ℂ) * stateEntry w.2 x y).sum =
          ∑ k, f k (x 0, x 1) * conj (f k (y 0, y 1))) ∧
      ∑ k, Gn (d 0) (d 1) (f k) ≤ (l.map fun w => w.1 * E w.2).sum + ε := by
  induction l generalizing ε with
  | nil => exact ⟨Empty, inferInstance, fun e => e.elim, fun x y _ _ => by simp, by simp [hε.le]⟩
  | cons w l ih =>
    obtain ⟨ι, _, f, hl, hv⟩ := ih (fun v hv => hd v (List.mem_cons_of_mem _ hv))
      (fun v hv => h0 v (List.mem_cons_of_mem _ hv)) (half_pos hε)
    rcases (h0 w List.mem_cons_self).eq_or_lt with hw | hw
    · refine ⟨ι, inferInstance, f, fun x y hx hy => ?_, ?_⟩
      · rw [List.map_cons, List.sum_cons, ← hw, hl x y hx hy]; simp
      · rw [List.map_cons, List.sum_cons, ← hw, zero_mul, zero_add]; linarith
    obtain ⟨v, ⟨κ, _, f1, h1, rfl⟩, hvlt⟩ := exists_near w.2 (div_pos (half_pos hε) hw)
    have hdw := hd w List.mem_cons_self
    refine ⟨κ ⊕ ι, inferInstance,
      Sum.elim (fun k n => ((Real.sqrt w.1 : ℝ) : ℂ) * f1 k n) f, fun x y hx hy => ?_, ?_⟩
    · rw [List.map_cons, List.sum_cons, hl x y hx hy, Fintype.sum_sum_type,
        h1 x y (fun i => hdw ▸ hx i) (fun i => hdw ▸ hy i), Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      have hs : ((Real.sqrt w.1 : ℝ) : ℂ) * ((Real.sqrt w.1 : ℝ) : ℂ) = (w.1 : ℂ) := by
        exact_mod_cast Real.mul_self_sqrt hw.le
      simp only [Sum.elim_inl, map_mul, Complex.conj_ofReal]
      rw [← hs]; ring
    · rw [Fintype.sum_sum_type, List.map_cons, List.sum_cons]
      simp only [Sum.elim_inl, Sum.elim_inr]
      have e : ∑ k, Gn (d 0) (d 1) (fun n => ((Real.sqrt w.1 : ℝ) : ℂ) * f1 k n) =
          w.1 * ∑ k, Gn (w.2.dims 0) (w.2.dims 1) (f1 k) := by
        rw [Finset.mul_sum, hdw]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Gn_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
          Real.sq_sqrt hw.le]
      rw [e]
      have : w.1 * ∑ k, Gn (w.2.dims 0) (w.2.dims 1) (f1 k) < w.1 * E w.2 + ε / 2 := by
        have := mul_lt_mul_of_pos_left hvlt hw
        rwa [mul_add, mul_div_cancel₀ _ hw.ne'] at this
      linarith

/-! ### the LOCC tree -/

lemma sum_flat {S : Type} (k : ℕ) (F : Fin k → List (ℝ × S)) (g : ℝ × S → ℝ) :
    (((List.finRange k).flatMap F).map g).sum = ∑ j, ((F j).map g).sum := by
  rw [List.map_flatMap, List.flatMap, List.sum_flatten, List.map_map, Fin.sum_univ_def]
  rfl

theorem roof_main {s : Shared} {out : List (ℝ × Shared)} (h : LocalTree s out) :
    ∀ val, Dec s val → (out.map fun w => w.1 * E w.2).sum ≤ val := by
  induction h with
  | stop s => intro val hv; simpa using E_le hv
  | step s k p r hI next hn ih =>
    intro val hv
    obtain ⟨vj, hvj, hsum⟩ := step_dec hI hv
    rw [sum_flat]
    refine le_trans (Finset.sum_le_sum fun j _ => ?_) hsum
    rw [List.map_map]
    have e : ((next j).map ((fun w : ℝ × Shared => w.1 * E w.2) ∘ fun w => (p j * w.1, w.2))).sum =
        p j * ((next j).map fun w => w.1 * E w.2).sum := by
      rw [← List.sum_map_mul_left]
      congr 1
      exact List.map_congr_left fun w _ => by simp [mul_assoc]
    rw [e]
    rcases (hI.1 j).eq_or_lt with h0 | h0
    · rw [← h0]; simp
    · exact mul_le_mul_of_nonneg_left (ih j (vj j) (hvj j h0)) h0.le
  | forget s t out hl hd hmix ih =>
    intro val hv
    have hw0 := (X4ZE.main hl).1
    have key : E t ≤ (out.map fun w => w.1 * E w.2).sum := by
      refine le_of_forall_pos_lt_add fun ε hε => ?_
      obtain ⟨ι, _, f, hf, hle⟩ := mix t.dims out hd hw0 (half_pos hε)
      have hD : Dec t (∑ k, Gn (t.dims 0) (t.dims 1) (f k)) :=
        ⟨ι, inferInstance, f, fun x y hx hy => by rw [hmix, hf x y hx hy], rfl⟩
      linarith [E_le hD]
    simpa using key.trans (ih val hv)

/-- conjunct 5 of `local_entropy_bounds`. -/
theorem part5 (s : Shared) (hs : IsPureShared s) (out : List (ℝ × Shared)) (hl : LocalTree s out)
    (hpure : ∀ w ∈ out, 0 < w.1 → IsPureShared w.2) :
    (out.map fun w => w.1 * ent w.2).sum ≤ ent s := by
  obtain ⟨v, hv⟩ := Dec_exists s
  have hvs := dec_pure hs hv
  have hw0 := (X4ZE.main hl).1
  have e : (out.map fun w => w.1 * ent w.2).sum = (out.map fun w => w.1 * E w.2).sum := by
    congr 1
    refine List.map_congr_left fun w hw => ?_
    rcases (hw0 w hw).eq_or_lt with h | h
    · rw [← h]; simp
    · rw [E_pure (hpure w hw h)]
  rw [e, ← hvs]
  exact roof_main hl v hv

end X4LE

end

-- ===== LESol =====

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P42

open scoped BigOperators Matrix ComplexConjugate

open MeasureTheory ProbabilityTheory

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the exact accepted objects, without introducing same-name aliases.

open Information100.P21 (Op Vec FiniteLOCC)

open Dependency50.P42 (dimensionedPower singlets)

open Dependency50.P48 (pureFidelity)

open Gap48.P32 (pairOfState)

open Next46.P39 (rectAct)

/-- PDF p.6: entropy interval, unconditional no-signalling marginal, unitary
marginal/spectral invariance, and the iterated pure-output upper bound.
Refined Kraus outcomes keep the complete conditional joint state pure. -/
theorem local_entropy_bounds_x4 {a b c k : ℕ} (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (psi : Vec (Fin a × Fin b)) (hnorm : ‖psi‖=1)
    (A : Fin k → Matrix (Fin c) (Fin a) ℂ) (hA : IsKrausFamily A) :
    let p := fun j => ‖aliceKetBranch (A j) psi‖^2
    let rho := fun j => ((p j : ℂ)⁻¹) • pureDensity (aliceKetBranch (A j) psi)
    (∑ j, (p j : ℂ) • traceLeft (rho j))=traceLeft (pureDensity psi) ∧
    vnEntropy (traceLeft (pureDensity psi))-outcomeEntropy p≤
      (∑ j, p j*vnEntropy (traceLeft (rho j))) ∧
    (∑ j, p j*vnEntropy (traceLeft (rho j)))≤vnEntropy (traceLeft (pureDensity psi)) ∧
    (∀ U : Matrix.unitaryGroup (Fin a) ℂ,
      traceLeft (pureDensity (aliceKetBranch (U : Op (Fin a)) psi))=traceLeft (pureDensity psi) ∧
      traceRight (pureDensity (aliceKetBranch (U : Op (Fin a)) psi))=
        (U : Op (Fin a))*traceRight (pureDensity psi)*(U : Op (Fin a))ᴴ) ∧
    (∀ s : Shared, IsPureShared s → ∀ out : List (ℝ × Shared), LocalTree s out →
      (∀ w∈out, 0<w.1 → IsPureShared w.2) →
        (out.map fun w => w.1*ent w.2).sum≤ent s) := by
  intro p rho
  have hA' : ∑ j, (A j)ᴴ * A j = 1 := hA
  have hsum := X4LE.tl_sum (b := b) (fun _ => c) A (by convert hA') psi
  have hp : ∀ j, p j = ‖aliceKetBranch (A j) psi‖ ^ 2 := fun j => rfl
  have hv0 : ∀ j, p j = 0 → aliceKetBranch (A j) psi = 0 := by
    intro j h
    rw [hp j] at h
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h)
  have hpd0 : ∀ {α : Type}, pureDensity (0 : Vec α) = 0 := by
    intro α; ext; simp [pureDensity]
  have htl0 : ∀ {α β : Type} [Fintype α], traceLeft (0 : Matrix (α × β) (α × β) ℂ) = 0 := by
    intro α β _; ext; simp [traceLeft]
  have hσ : ∀ j, (p j : ℂ) • traceLeft (rho j) = traceLeft (pureDensity (aliceKetBranch (A j) psi)) := by
    intro j
    simp only [rho, X4LE.tl_smul, smul_smul]
    rcases eq_or_ne (p j) 0 with h | h
    · rw [hv0 j h, hpd0, htl0]; simp
    · rw [mul_inv_cancel₀ (by exact_mod_cast h), one_smul]
  have hT : ∀ j, p j * vnEntropy (traceLeft (rho j)) =
      vnEntropy (traceLeft (pureDensity (aliceKetBranch (A j) psi))) + p j * Real.logb 2 (p j) := by
    intro j
    rcases eq_or_ne (p j) 0 with h | h
    · rw [h, hv0 j h, hpd0, htl0, X4LE.vn_zero]; simp
    · have hpos : 0 < p j := lt_of_le_of_ne (by rw [hp j]; positivity) (Ne.symm h)
      simp only [rho, X4LE.tl_smul]
      rw [show ((p j : ℂ))⁻¹ = (((p j)⁻¹ : ℝ) : ℂ) by push_cast; rfl,
        X4LE.vn_smul (X4LE.tl_psd _).1 (inv_pos.2 hpos), X4LE.tl_trace_re, ← hp j, Real.logb_inv]
      field_simp
      ring
  have htr1 : ∑ j, (traceLeft (pureDensity (aliceKetBranch (A j) psi))).trace = 1 := by
    rw [← Matrix.trace_sum, hsum, X4LE.tl_trace, hnorm]; simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [hσ]; exact hsum
  · have h1 := X4LE.subconc (fun j => traceLeft (pureDensity (aliceKetBranch (A j) psi)))
      (fun j => X4LE.tl_psd _)
    rw [hsum] at h1
    simp only [hT, Finset.sum_add_distrib, outcomeEntropy]
    linarith
  · have h1 := X4LE.conc (fun j => traceLeft (pureDensity (aliceKetBranch (A j) psi)))
      (fun j => X4LE.tl_psd _) htr1
    rw [hsum] at h1
    simp only [X4LE.tl_trace_re, ← hp] at h1
    simp only [hT]
    exact h1
  · intro U
    have hU : (U : Op (Fin a))ᴴ * (U : Op (Fin a)) = 1 := by
      rw [← Matrix.star_eq_conjTranspose]; exact Unitary.star_mul_self_of_mem U.2
    constructor
    · rw [X4LE.tl_eq, X4LE.tl_eq, X4LE.Mv_akb, Matrix.conjTranspose_mul, Matrix.mul_assoc,
        ← Matrix.mul_assoc _ (U : Op (Fin a)), hU, Matrix.one_mul]
    · rw [X4LE.tr_eq, X4LE.tr_eq, X4LE.Mv_akb, Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
  · intro s hs out hl hpure
    exact X4LE.part5 s hs out hl hpure


/-- PDF p.6: entropy interval, unconditional no-signalling marginal, unitary
marginal/spectral invariance, and the iterated pure-output upper bound.
Refined Kraus outcomes keep the complete conditional joint state pure. -/
theorem _root_.solution {a b c k : ℕ} (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (psi : Vec (Fin a × Fin b)) (hnorm : ‖psi‖=1)
    (A : Fin k → Matrix (Fin c) (Fin a) ℂ) (hA : IsKrausFamily A) :
    let p := fun j => ‖aliceKetBranch (A j) psi‖^2
    let rho := fun j => ((p j : ℂ)⁻¹) • pureDensity (aliceKetBranch (A j) psi)
    (∑ j, (p j : ℂ) • traceLeft (rho j))=traceLeft (pureDensity psi) ∧
    vnEntropy (traceLeft (pureDensity psi))-outcomeEntropy p≤
      (∑ j, p j*vnEntropy (traceLeft (rho j))) ∧
    (∑ j, p j*vnEntropy (traceLeft (rho j)))≤vnEntropy (traceLeft (pureDensity psi)) ∧
    (∀ U : Matrix.unitaryGroup (Fin a) ℂ,
      traceLeft (pureDensity (aliceKetBranch (U : Op (Fin a)) psi))=traceLeft (pureDensity psi) ∧
      traceRight (pureDensity (aliceKetBranch (U : Op (Fin a)) psi))=
        (U : Op (Fin a))*traceRight (pureDensity psi)*(U : Op (Fin a))ᴴ) ∧
    (∀ s : Shared, IsPureShared s → ∀ out : List (ℝ × Shared), LocalTree s out →
      (∀ w∈out, 0<w.1 → IsPureShared w.2) →
        (out.map fun w => w.1*ent w.2).sum≤ent s) :=
  local_entropy_bounds_x4 ha hb hc psi hnorm A hA

end QAlgorithms.Papers.Independent.Support50.P42

end

