-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P02.degradable_concavity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:08:26.90925+00:00
-- url     : https://prove2.me/submissions/b67186d8-bcf6-431f-8621-24120981e2d3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P41
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P42
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P20
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P24
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P20_strongSubadditivity
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P02

-- ===== ULib =====

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
theorem x4_tr_aeval {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (p : ℝ[X]) :
    (aeval M p).trace = ∑ i ∈ Finset.range (p.natDegree + 1), (p.coeff i : ℂ) * (M ^ i).trace := by
  rw [aeval_eq_sum_range, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.trace_smul]
  simp [Complex.real_smul]

theorem x4_tr_cfc_eq {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
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

theorem x4_pow_mul {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (V : Matrix ι κ ℂ) (W : Matrix κ ι ℂ) (k : ℕ) :
    (V * W) ^ (k + 1) = V * (W * V) ^ k * W := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [Matrix.mul_assoc]

theorem x4_tr_pow_swap {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (V : Matrix ι κ ℂ) (W : Matrix κ ι ℂ) (k : ℕ) (hk : 1 ≤ k) :
    ((V * W) ^ k).trace = ((W * V) ^ k).trace := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
  rw [x4_pow_mul, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, ← pow_succ]

/-- tr f(V Vᴴ) = tr f((Vᴴ V)ᵀ) when f 0 = 0. -/
theorem x4_ent_swap {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (V : Matrix ι κ ℂ) :
    QAlgorithms.vnEntropy (V * Vᴴ) = QAlgorithms.vnEntropy ((Vᴴ * V)ᵀ) := by
  unfold QAlgorithms.vnEntropy
  rw [x4_tr_cfc_eq (V * Vᴴ) ((Vᴴ * V)ᵀ) (isHermitian_mul_conjTranspose_self V)
    (isHermitian_conjTranspose_mul_self V).transpose _ _ (by simp)]
  intro k hk
  rw [← Matrix.transpose_pow, Matrix.trace_transpose, x4_tr_pow_swap _ _ k hk]

variable {d m : ℕ}

/-- the coefficient matrix `V_{(r,y),k} = ((1 ⊗ A_k) ψ)(r,y)` -/
def Vm {R : Type*} [Fintype R] (A : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (psi : EuclideanSpace ℂ (R × Fin d)) : Matrix (R × Fin d) (Fin m) ℂ :=
  fun p k => ∑ i, A k p.2 i * psi (p.1, i)

lemma idT_eq {R : Type*} [Fintype R] (A : Fin m → Matrix (Fin d) (Fin d) ℂ)
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

lemma gram_eq {R : Type*} [Fintype R] (A : Fin m → Matrix (Fin d) (Fin d) ℂ)
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
theorem ent_core {R : Type*} [Fintype R] (A : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (psi : EuclideanSpace ℂ (R × Fin d)) (rho : Matrix (Fin d) (Fin d) ℂ)
    (hK : ∀ j j', ∑ r, psi (r, j) * conj (psi (r, j')) = rho j j') :
    vnEntropy (idTensorSuperop (R := R) (krausApply A) (pureDensity psi)) =
      vnEntropy (Matrix.of fun k l => (A k * rho * (A l)ᴴ).trace) := by
  rw [idT_eq, x4_ent_swap, gram_eq A psi rho hK]

lemma sqrt_gram {I : Type*} [Fintype I] [DecidableEq I] (rho : Matrix I I ℂ) (hrho : rho.PosSemidef)
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
lemma orth_ent {ι T : Type*} [Fintype ι] [DecidableEq ι] [Fintype T] [DecidableEq T]
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
def amp {ι : Type*} [Fintype ι] [DecidableEq ι] {σ : Matrix ι ι ℂ} (hσ : σ.PosSemidef) (k a : ι) : ℂ :=
  ((Real.sqrt (hσ.1.eigenvalues k) : ℝ) : ℂ) * hσ.1.eigenvectorBasis k a

lemma amp_decomp {ι : Type*} [Fintype ι] [DecidableEq ι] {σ : Matrix ι ι ℂ} (hσ : σ.PosSemidef) :
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

lemma amp_inner {ι : Type*} [Fintype ι] [DecidableEq ι] {σ : Matrix ι ι ℂ} (hσ : σ.PosSemidef)
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

lemma amp_norm {ι : Type*} [Fintype ι] [DecidableEq ι] {σ : Matrix ι ι ℂ} (hσ : σ.PosSemidef)
    (k : ι) : ∑ a, ‖amp hσ k a‖ ^ 2 = hσ.1.eigenvalues k := by
  have h := amp_inner hσ k k
  rw [if_pos rfl] at h
  have : ((∑ a, ‖amp hσ k a‖ ^ 2 : ℝ) : ℂ) = ∑ a, amp hσ k a * conj (amp hσ k a) := by
    push_cast
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  exact_mod_cast this.trans h

lemma vn_amp {ι : Type*} [Fintype ι] [DecidableEq ι] {σ : Matrix ι ι ℂ} (hσ : σ.PosSemidef) :
    vnEntropy σ = -∑ k, hσ.1.eigenvalues k * Real.logb 2 (hσ.1.eigenvalues k) := by
  rw [X4ZE.vn_eig hσ.1, Finset.sum_div, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun k _ => nml _

/-- finite mixtures of rank-one terms: entropy ≤ Shannon entropy of the weights. -/
lemma fin_bound {ι T : Type*} [Fintype ι] [DecidableEq ι] [Fintype T] [DecidableEq T]
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
theorem subconc {ι M : Type*} [Fintype ι] [DecidableEq ι] [Fintype M] [DecidableEq M]
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
def blk {ι M : Type*} [DecidableEq M] (σ : M → Matrix ι ι ℂ) : Matrix (M × ι) (M × ι) ℂ :=
  fun x y => if x.1 = y.1 then σ x.1 x.2 y.2 else 0

lemma blk_decomp {ι M : Type*} [Fintype ι] [DecidableEq ι] [Fintype M] [DecidableEq M]
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

lemma vn_blk {ι M : Type*} [Fintype ι] [DecidableEq ι] [Fintype M] [DecidableEq M]
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
theorem conc {ι M : Type*} [Fintype ι] [DecidableEq ι] [Fintype M] [DecidableEq M]
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
def Mv {α β : Type*} (v : EuclideanSpace ℂ (α × β)) : Matrix α β ℂ := Matrix.of fun x y => v (x, y)

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

lemma tl_eq {α β : Type*} [Fintype α] [Fintype β] (v : EuclideanSpace ℂ (α × β)) :
    traceLeft (pureDensity v) = ((Mv v)ᴴ * Mv v)ᵀ := by
  ext y y'
  simp [traceLeft, pureDensity, Mv, Matrix.mul_apply, mul_comm]

lemma tr_eq {α β : Type*} [Fintype α] [Fintype β] (v : EuclideanSpace ℂ (α × β)) :
    traceRight (pureDensity v) = Mv v * (Mv v)ᴴ := by
  ext y y'
  simp [traceRight, pureDensity, Mv, Matrix.mul_apply]

lemma tl_psd {α β : Type*} [Fintype α] [Fintype β] (v : EuclideanSpace ℂ (α × β)) :
    (traceLeft (pureDensity v)).PosSemidef := by
  rw [tl_eq]; exact (posSemidef_conjTranspose_mul_self _).transpose

lemma tl_trace {α β : Type*} [Fintype α] [Fintype β] (v : EuclideanSpace ℂ (α × β)) :
    (traceLeft (pureDensity v)).trace = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
  rw [EuclideanSpace.norm_sq_eq]
  push_cast
  simp only [Matrix.trace, traceLeft, pureDensity, Matrix.diag, Matrix.of_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl

lemma tl_trace_re {α β : Type*} [Fintype α] [Fintype β] (v : EuclideanSpace ℂ (α × β)) :
    (traceLeft (pureDensity v)).trace.re = ‖v‖ ^ 2 := by
  rw [tl_trace]; exact_mod_cast Complex.ofReal_re _

lemma vn_zero {ι : Type*} [Fintype ι] [DecidableEq ι] : vnEntropy (0 : Matrix ι ι ℂ) = 0 := by
  unfold vnEntropy; simp

lemma tl_smul {α β : Type*} [Fintype α] (c : ℂ) (M : Matrix (α × β) (α × β) ℂ) :
    traceLeft (c • M) = c • traceLeft M := by
  ext; simp [traceLeft, Finset.mul_sum]

lemma pd_smul {α : Type*} (c : ℂ) (v : EuclideanSpace ℂ α) :
    pureDensity (c • v) = ((‖c‖ ^ 2 : ℝ) : ℂ) • pureDensity v := by
  ext x y
  simp only [pureDensity, Matrix.of_apply, Matrix.smul_apply, PiLp.smul_apply, smul_eq_mul, map_mul]
  have : c * conj c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [← this]; ring

/-- Kraus completeness: the Bob marginal is unchanged on average. -/
lemma tl_sum {M : Type*} [Fintype M] (c : M → ℕ) (A : ∀ m, Matrix (Fin (c m)) (Fin a) ℂ)
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
def Gv {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] (v : EuclideanSpace ℂ (α × β)) : ℝ :=
  vnEntropy (traceLeft (pureDensity v)) + ‖v‖ ^ 2 * Real.logb 2 (‖v‖ ^ 2)

lemma Gv_zero {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] :
    Gv (0 : EuclideanSpace ℂ (α × β)) = 0 := by
  have : pureDensity (0 : EuclideanSpace ℂ (α × β)) = 0 := by ext; simp [pureDensity]
  have h2 : traceLeft (0 : Matrix (α × β) (α × β) ℂ) = 0 := by ext; simp [traceLeft]
  simp [Gv, this, h2, vn_zero]

lemma Gv_smul {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] (z : ℂ)
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

lemma Gv_unit {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] (v : EuclideanSpace ℂ (α × β))
    (hv : ‖v‖ = 1) : Gv v = vnEntropy (traceLeft (pureDensity v)) := by
  simp [Gv, hv]

lemma Gv_branch {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] (v : EuclideanSpace ℂ (α × β)) :
    Gv v = vnEntropy (traceLeft (pureDensity v)) +
      (traceLeft (pureDensity v)).trace.re * Real.logb 2 (traceLeft (pureDensity v)).trace.re := by
  rw [tl_trace_re]; rfl

/-- monotonicity of `Gv` under any Alice-side Kraus family (outputs may differ). -/
theorem mono {M : Type*} [Fintype M] [DecidableEq M] (c : M → ℕ)
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
def swapV {α β : Type*} (v : EuclideanSpace ℂ (α × β)) : EuclideanSpace ℂ (β × α) :=
  WithLp.toLp 2 fun p => v (p.2, p.1)

lemma norm_swapV {α β : Type*} [Fintype α] [Fintype β] (v : EuclideanSpace ℂ (α × β)) :
    ‖swapV v‖ = ‖v‖ := by
  have : ‖swapV v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type,
      Fintype.sum_prod_type, Finset.sum_comm]
    rfl
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this

lemma Gv_swap {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (v : EuclideanSpace ℂ (α × β)) : Gv (swapV v) = Gv v := by
  unfold Gv
  rw [norm_swapV]
  congr 1
  have e1 : traceLeft (pureDensity (swapV v)) = Mv v * (Mv v)ᴴ := by
    ext; simp [traceLeft, pureDensity, swapV, Mv, Matrix.mul_apply]
  rw [e1, X4KF.x4_ent_swap, tl_eq]

end X4LE

end

-- ===== ERA =====

/-! Generic entropy facts: scaling with `c ≥ 0`, additivity on orthogonal PSD summands,
invariance under isometric conjugation, pure states, and the qubit bound `S ≤ 1`. -/

noncomputable section

namespace X4ER
open Matrix Real QAlgorithms
open scoped Matrix ComplexConjugate ComplexOrder

lemma vn_smul0 {ι : Type*} [Fintype ι] [DecidableEq ι] {X : Matrix ι ι ℂ} (hX : X.IsHermitian)
    {c : ℝ} (hc : 0 ≤ c) :
    vnEntropy ((c : ℂ) • X) = c * vnEntropy X - c * Real.logb 2 c * X.trace.re := by
  rcases hc.eq_or_lt with rfl | hc'
  · simp [X4LE.vn_zero]
  · exact X4LE.vn_smul hX hc'

lemma amp_orth {ι : Type*} [Fintype ι] [DecidableEq ι] {X Y : Matrix ι ι ℂ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) (hXY : X * Y = 0) (k l : ι) :
    ∑ a, X4LE.amp hX k a * conj (X4LE.amp hY l a) = 0 := by
  set v := hX.1.eigenvectorBasis k
  set w := hY.1.eigenvectorBasis l
  set lam := hX.1.eigenvalues k
  set mu := hY.1.eigenvalues l
  have hv : ∀ a, ∑ b, X a b * v b = lam * v a := by
    intro a
    have := congrFun (hX.1.mulVec_eigenvectorBasis k) a
    simpa [Matrix.mulVec, dotProduct] using this
  have hw : ∀ a, ∑ b, Y a b * w b = mu * w a := by
    intro a
    have := congrFun (hY.1.mulVec_eigenvectorBasis l) a
    simpa [Matrix.mulVec, dotProduct] using this
  have key : ((lam : ℂ) * mu) * ∑ a, v a * conj (w a) = 0 := by
    have e1 : ((lam : ℂ) * mu) * ∑ a, v a * conj (w a) =
        ∑ a, (∑ b, X a b * v b) * conj (∑ c, Y a c * w c) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hv a, hw a, map_mul, Complex.conj_ofReal]; ring
    rw [e1]
    have e2 : ∀ a, (∑ b, X a b * v b) * conj (∑ c, Y a c * w c) =
        ∑ b, ∑ c, v b * conj (w c) * (conj (X b a) * conj (Y a c)) := by
      intro a
      rw [map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
      have hx : X a b = conj (X b a) := by
        have := congrFun (congrFun hX.1.eq b) a
        rw [conjTranspose_apply] at this
        rw [← this]; simp
      rw [hx, map_mul]; ring
    simp only [e2]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [← Finset.mul_sum]
    have : ∑ a, conj (X b a) * conj (Y a c) = conj ((X * Y) b c) := by
      rw [Matrix.mul_apply, map_sum]; simp [map_mul]
    rw [this, hXY]; simp
  have e : ∑ a, X4LE.amp hX k a * conj (X4LE.amp hY l a) =
      ((Real.sqrt lam : ℝ) : ℂ) * ((Real.sqrt mu : ℝ) : ℂ) * ∑ a, v a * conj (w a) := by
    simp only [X4LE.amp, map_mul, Complex.conj_ofReal, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => by ring
  rw [e]
  by_cases h0 : (lam : ℂ) * mu = 0
  · rcases mul_eq_zero.1 h0 with h | h
    · have : lam = 0 := by exact_mod_cast h
      simp [this]
    · have : mu = 0 := by exact_mod_cast h
      simp [this]
  · rw [(mul_eq_zero.1 key).resolve_left h0, mul_zero]

/-- entropy is additive on PSD summands with orthogonal supports. -/
lemma vn_add_orth {ι : Type*} [Fintype ι] [DecidableEq ι] {X Y : Matrix ι ι ℂ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) (hXY : X * Y = 0) :
    vnEntropy (X + Y) = vnEntropy X + vnEntropy Y := by
  have hYX : Y * X = 0 := by
    have := congrArg conjTranspose hXY
    rwa [conjTranspose_mul, hX.1.eq, hY.1.eq, conjTranspose_zero] at this
  set φ : ι ⊕ ι → ι → ℂ := fun t => Sum.elim (X4LE.amp hX) (X4LE.amp hY) t
  have hdec : X + Y = ∑ t, Matrix.of fun a b => φ t a * conj (φ t b) := by
    conv_lhs => rw [X4LE.amp_decomp hX, X4LE.amp_decomp hY]
    rw [Fintype.sum_sum_type]; rfl
  have horth : ∀ t t', t ≠ t' → ∑ i, φ t i * conj (φ t' i) = 0 := by
    intro t t' htt
    rcases t with k | k <;> rcases t' with l | l
    · simp only [φ, Sum.elim_inl]
      rw [X4LE.amp_inner, if_neg (fun h => htt (by rw [h]))]
    · exact amp_orth hX hY hXY k l
    · exact amp_orth hY hX hYX k l
    · simp only [φ, Sum.elim_inr]
      rw [X4LE.amp_inner, if_neg (fun h => htt (by rw [h]))]
  rw [hdec, X4LE.orth_ent φ horth, Fintype.sum_sum_type, X4LE.vn_amp hX, X4LE.vn_amp hY]
  simp only [φ, Sum.elim_inl, Sum.elim_inr, X4LE.amp_norm]
  ring

/-- entropy is invariant under conjugation by an isometry. -/
lemma vn_conj_iso {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {X : Matrix ι ι ℂ} (hX : X.PosSemidef) (J : Matrix κ ι ℂ) (hJ : Jᴴ * J = 1) :
    vnEntropy (J * X * Jᴴ) = vnEntropy X := by
  set V : Matrix ι ι ℂ := Matrix.of fun a k => X4LE.amp hX k a
  have hV : X = V * Vᴴ := by
    conv_lhs => rw [X4LE.amp_decomp hX]
    ext a b; simp [V, Matrix.mul_apply, Matrix.sum_apply, conjTranspose_apply]
  have h1 : J * X * Jᴴ = (J * V) * (J * V)ᴴ := by
    rw [hV, conjTranspose_mul]; simp only [Matrix.mul_assoc]
  have h2 : (J * V)ᴴ * (J * V) = Vᴴ * V := by
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Jᴴ, hJ, Matrix.one_mul]
  rw [h1, X4KF.x4_ent_swap, h2, ← X4KF.x4_ent_swap, ← hV]

lemma vn_pure {ι : Type*} [Fintype ι] [DecidableEq ι] (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) :
    vnEntropy (pureDensity ψ) = 0 := by
  have h : pureDensity ψ = ∑ _t : Unit, Matrix.of fun a b => ψ a * conj (ψ b) := by
    simp [pureDensity]
  rw [h, X4LE.orth_ent (fun _ a => ψ a) (fun t t' h => absurd (Subsingleton.elim t t') h)]
  have : ∑ i, ‖ψ i‖ ^ 2 = 1 := by rw [← EuclideanSpace.norm_sq_eq, hψ, one_pow]
  simp [this]

lemma qubit_le {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : X.PosSemidef) (htr : X.trace = 1) :
    vnEntropy X ≤ 1 := by
  rw [X4LE.vn_amp hX, Fin.sum_univ_two]
  have hs : hX.1.eigenvalues 0 + hX.1.eigenvalues 1 = 1 := by
    have := hX.1.trace_eq_sum_eigenvalues
    rw [htr, Fin.sum_univ_two] at this
    have h2 := congrArg Complex.re this
    simpa using h2.symm
  set p := hX.1.eigenvalues 0
  have h1 : hX.1.eigenvalues 1 = 1 - p := by linarith
  rw [h1]
  have hb := Real.binEntropy_le_log_two (p := p)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have : -(p * Real.logb 2 p + (1 - p) * Real.logb 2 (1 - p)) = Real.binEntropy p / Real.log 2 := by
    simp only [Real.binEntropy, Real.log_inv, Real.logb]; field_simp; ring
  rw [this, div_le_one hl2]; exact hb

end X4ER

end

-- ===== QSQ =====

/-! Extensions of a pure multipartite state are products `ψψ† ⊗ τ`; complementary
register marginals of the pure part have equal entropy, so the total and dual
conditional informations agree on every extension. -/

noncomputable section

namespace X4QS
open Matrix QAlgorithms Real
open scoped Matrix ComplexConjugate ComplexOrder Kronecker
open QAlgorithms.Papers.Independent.Claimed50.P33

/-- `S(X ⊗ Y) = S(X) tr Y + tr X S(Y)` for PSD `X`, `Y`. -/
lemma vn_kron {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {X : Matrix ι ι ℂ} {Y : Matrix κ κ ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    vnEntropy (X ⊗ₖ Y) = vnEntropy X * Y.trace.re + X.trace.re * vnEntropy Y := by
  set φ : ι × κ → ι × κ → ℂ := fun t p => X4LE.amp hX t.1 p.1 * X4LE.amp hY t.2 p.2
  have hdec : X ⊗ₖ Y = ∑ t, Matrix.of fun a b => φ t a * conj (φ t b) := by
    conv_lhs => rw [X4LE.amp_decomp hX, X4LE.amp_decomp hY]
    ext ⟨a1, a2⟩ ⟨b1, b2⟩
    simp only [kroneckerMap_apply, Matrix.sum_apply, Matrix.of_apply, φ, Fintype.sum_prod_type,
      Finset.sum_mul_sum, map_mul]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  have horth : ∀ t t', t ≠ t' → ∑ p, φ t p * conj (φ t' p) = 0 := by
    intro t t' htt
    have e : ∑ p, φ t p * conj (φ t' p) =
        (∑ a, X4LE.amp hX t.1 a * conj (X4LE.amp hX t'.1 a)) *
          (∑ b, X4LE.amp hY t.2 b * conj (X4LE.amp hY t'.2 b)) := by
      simp only [φ, Fintype.sum_prod_type, Finset.sum_mul_sum, map_mul]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
    rw [e, X4LE.amp_inner, X4LE.amp_inner]
    obtain ⟨t1, t2⟩ := t; obtain ⟨t1', t2'⟩ := t'
    by_cases h1 : t1 = t1'
    · have h2 : t2 ≠ t2' := fun h2 => htt (by rw [h1, h2])
      simp [h2]
    · simp [h1]
  have hnorm : ∀ t : ι × κ, ∑ p, ‖φ t p‖ ^ 2 = hX.1.eigenvalues t.1 * hY.1.eigenvalues t.2 := by
    intro t
    simp only [φ, norm_mul, mul_pow, Fintype.sum_prod_type, ← Finset.sum_mul_sum,
      X4LE.amp_norm]
  rw [hdec, X4LE.orth_ent φ horth]
  simp only [hnorm]
  rw [X4LE.vn_amp hX, X4LE.vn_amp hY, hX.1.trace_eq_sum_eigenvalues,
    hY.1.trace_eq_sum_eigenvalues]
  simp only [Complex.re_sum, Complex.ofReal_re, Fintype.sum_prod_type]
  have key : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
      x * y * Real.logb 2 (x * y) = y * (x * Real.logb 2 x) + x * (y * Real.logb 2 y) := by
    intro x y hx hy
    rcases hx.eq_or_lt with rfl | hx'
    · simp
    rcases hy.eq_or_lt with rfl | hy'
    · simp
    rw [Real.logb_mul hx'.ne' hy'.ne']; ring
  simp only [fun j k => key _ _ (hX.eigenvalues_nonneg j) (hY.eigenvalues_nonneg k),
    Finset.sum_add_distrib, neg_mul, ← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_neg_distrib]
  have e1 : ∀ x : ℝ, (RCLike.ofReal x : ℂ).re = x := fun x => rfl
  simp only [e1]
  ring

variable {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]

/-- glue an assignment on `s` with one on its complement `u`. -/
def merge {s u : Finset (Fin m)} (h : ∀ i, i ∈ u ↔ i ∉ s) (a : SubBasis D s) (z : SubBasis D u) :
    RegisterBasis D :=
  fun i => if hi : i ∈ s then a ⟨i, hi⟩ else z ⟨i, (h i).2 hi⟩

lemma merge_comm {s u : Finset (Fin m)} (h : ∀ i, i ∈ u ↔ i ∉ s) (h' : ∀ i, i ∈ s ↔ i ∉ u)
    (a : SubBasis D s) (z : SubBasis D u) : merge h' z a = merge h a z := by
  funext i
  simp only [merge]
  by_cases hs : i ∈ s
  · have hu : i ∉ u := (h' i).1 hs
    simp [hs, hu]
  · have hu : i ∈ u := (h i).2 hs
    simp [hs, hu]

lemma sum_marg {M : Type*} [AddCommMonoid M] {s u : Finset (Fin m)} (h : ∀ i, i ∈ u ↔ i ∉ s)
    (a b : SubBasis D s) (F : RegisterBasis D → RegisterBasis D → M) (P : RegisterBasis D → RegisterBasis D → Prop)
    {inst : ∀ x y, Decidable (P x y)}
    (hP : ∀ x y, P x y ↔ ((∀ i (hi : i ∈ s), x i = a ⟨i,hi⟩ ∧ y i = b ⟨i,hi⟩) ∧ (∀ i, i ∉ s → x i = y i))) :
    ∑ x, ∑ y, (if P x y then F x y else 0) = ∑ z : SubBasis D u, F (merge h a z) (merge h b z) := by
  classical
  let r : RegisterBasis D → SubBasis D u := fun x i => x i.1
  have inner : ∀ x, ∑ y, (if P x y then F x y else 0) =
      if (∀ i (hi : i ∈ s), x i = a ⟨i,hi⟩) then F x (merge h b (r x)) else 0 := by
    intro x
    have hc : ∀ y, P x y ↔ ((∀ i (hi : i ∈ s), x i = a ⟨i,hi⟩) ∧ y = merge h b (r x)) := by
      intro y
      rw [hP]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨fun i hi => (h1 i hi).1, ?_⟩
        funext i
        simp only [merge, r]
        split_ifs with hi
        · exact (h1 i hi).2
        · exact (h2 i hi).symm
      · rintro ⟨h1, rfl⟩
        refine ⟨fun i hi => ⟨h1 i hi, by simp [merge, hi]⟩, fun i hi => by simp [merge, hi, r]⟩
    rw [Finset.sum_congr rfl fun y _ => if_congr (hc y) rfl rfl]
    by_cases hx : ∀ i (hi : i ∈ s), x i = a ⟨i,hi⟩
    · rw [if_pos hx, Finset.sum_congr rfl fun y _ => if_congr (and_iff_right hx) rfl rfl]
      simp
    · rw [if_neg hx]; exact Finset.sum_eq_zero fun y _ => if_neg (fun h => hx h.1)
  simp only [inner]
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' r (merge h a) ?_ ?_ ?_ ?_ ?_
  · intros; exact Finset.mem_univ _
  · intro z _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro i hi; simp [merge, hi]
  · intro x hx
    replace hx := (Finset.mem_filter.1 (Finset.mem_coe.1 hx)).2
    funext i
    simp only [merge, r]
    split_ifs with hi
    · exact (hx i hi).symm
    · rfl
  · intro z _
    funext i
    have hi : i.1 ∉ s := (h i.1).1 i.2
    simp [r, merge, hi]
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    congr 1
    funext i
    simp only [merge, r]
    split_ifs with hi
    · exact hx i hi
    · rfl

/-- the reshaped pure amplitudes. -/
def P (ψ : RegisterBasis D → ℂ) {s u : Finset (Fin m)} (h : ∀ i, i ∈ u ↔ i ∉ s) :
    Matrix (SubBasis D s) (SubBasis D u) ℂ := Matrix.of fun a z => ψ (merge h a z)

/-- every extension of a pure state is a product. -/
lemma ext_prod {I E : Type} [Fintype I] [DecidableEq I] [Fintype E] [DecidableEq E]
    (ψ : EuclideanSpace ℂ I) (hψ : ‖ψ‖ = 1)
    (σ : Matrix (I × E) (I × E) ℂ) (hσ : σ.PosSemidef) (hf : forgetEnvironment σ = pureDensity ψ) :
    ∃ τ : Matrix E E ℂ, τ.PosSemidef ∧ ∀ x f y g, σ (x, f) (y, g) = ψ x * conj (ψ y) * τ f g := by
  have hv := X4ZE.unit_sum ψ hψ
  have hsplit0 : ∀ (kf : (I × E) × E) (a : I), X4LE.amp hσ kf.1 (a, kf.2) =
      (∑ b, conj (ψ b) * X4LE.amp hσ kf.1 (b, kf.2)) * ψ a := by
    intro kf
    refine X4ZE.rank1_split (fun a => ψ a) hv (fun kf a => X4LE.amp hσ kf.1 (a, kf.2)) ?_ kf
    intro a b
    have := congrFun (congrFun hf a) b
    simp only [forgetEnvironment, pureDensity, Matrix.of_apply] at this
    rw [← this]
    conv_lhs => enter [2, e]; rw [X4LE.amp_decomp hσ]
    simp only [Matrix.sum_apply, Matrix.of_apply, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  have hsplit : ∀ k f a, X4LE.amp hσ k (a, f) =
      (∑ b, conj (ψ b) * X4LE.amp hσ k (b, f)) * ψ a := fun k f a => hsplit0 (k, f) a
  set α : (I × E) → E → ℂ := fun k f => ∑ b, conj (ψ b) * X4LE.amp hσ k (b, f)
  refine ⟨Matrix.of fun f g => ∑ k, α k f * conj (α k g), ?_, ?_⟩
  · have : (Matrix.of fun f g => ∑ k, α k f * conj (α k g)) =
        (Matrix.of fun f k => α k f) * (Matrix.of fun f k => α k f)ᴴ := by
      ext f g; simp [Matrix.mul_apply, conjTranspose_apply]
    rw [this]; exact posSemidef_self_mul_conjTranspose _
  · intro x f y g
    conv_lhs => rw [X4LE.amp_decomp hσ]
    simp only [Matrix.sum_apply, Matrix.of_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hsplit k f x, hsplit k g y]
    simp only [map_mul, α]; ring

lemma marg_eq {e : Type} [Fintype e] (ψ : RegisterBasis D → ℂ) (τ : Matrix e e ℂ)
    (σ : Matrix (RegisterBasis D × e) (RegisterBasis D × e) ℂ)
    (hprod : ∀ x f y g, σ (x, f) (y, g) = ψ x * conj (ψ y) * τ f g)
    {s u : Finset (Fin m)} (h : ∀ i, i ∈ u ↔ i ∉ s) :
    registerMarginal σ s = (P ψ h * (P ψ h)ᴴ) ⊗ₖ τ := by
  ext ⟨a, f⟩ ⟨b, g⟩
  simp only [registerMarginal]
  refine (sum_marg h a b (fun x y => σ (x, f) (y, g)) _ (fun x y => Iff.rfl)).trans ?_
  simp only [hprod, kroneckerMap_apply, Matrix.mul_apply, conjTranspose_apply, P, Matrix.of_apply,
    RCLike.star_def, Finset.sum_mul]

open Classical in
lemma ent_eq {e : Type} [Fintype e] [DecidableEq e] (ψ : RegisterBasis D → ℂ) (τ : Matrix e e ℂ)
    (hτ : τ.PosSemidef)
    (σ : Matrix (RegisterBasis D × e) (RegisterBasis D × e) ℂ)
    (hprod : ∀ x f y g, σ (x, f) (y, g) = ψ x * conj (ψ y) * τ f g)
    {s u : Finset (Fin m)} (h : ∀ i, i ∈ u ↔ i ∉ s) :
    entropyAt σ s = vnEntropy (P ψ h * (P ψ h)ᴴ) * τ.trace.re +
      (P ψ h * (P ψ h)ᴴ).trace.re * vnEntropy τ := by
  classical
  unfold entropyAt
  rw [marg_eq ψ τ σ hprod h]
  convert vn_kron (posSemidef_self_mul_conjTranspose (P ψ h)) hτ

lemma swapP (ψ : RegisterBasis D → ℂ) {s u : Finset (Fin m)} (h : ∀ i, i ∈ u ↔ i ∉ s)
    (h' : ∀ i, i ∈ s ↔ i ∉ u) : P ψ h' = (P ψ h)ᵀ := by
  ext z a; simp [P, merge_comm h h']

open Classical in
lemma ent_compl {e : Type} [Fintype e] [DecidableEq e] (ψ : RegisterBasis D → ℂ) (τ : Matrix e e ℂ)
    (hτ : τ.PosSemidef)
    (σ : Matrix (RegisterBasis D × e) (RegisterBasis D × e) ℂ)
    (hprod : ∀ x f y g, σ (x, f) (y, g) = ψ x * conj (ψ y) * τ f g) (s : Finset (Fin m)) :
    entropyAt σ s = entropyAt σ sᶜ := by
  classical
  have h : ∀ i, i ∈ sᶜ ↔ i ∉ s := fun i => Finset.mem_compl
  have h' : ∀ i, i ∈ s ↔ i ∉ sᶜ := fun i => by simp
  rw [ent_eq ψ τ hτ σ hprod h, ent_eq ψ τ hτ σ hprod h', swapP ψ h h']
  have hG : (P ψ h)ᵀ * ((P ψ h)ᵀ)ᴴ = ((P ψ h)ᴴ * P ψ h)ᵀ := by
    ext z z'; simp [Matrix.mul_apply, conjTranspose_apply, mul_comm]
  rw [hG, ← X4KF.x4_ent_swap, Matrix.trace_transpose, Matrix.trace_mul_comm]

section
attribute [local instance] Classical.propDecidable Classical.decEq

theorem key (hm : 2 ≤ m) [∀ i, Nonempty (D i)] (ψ : EuclideanSpace ℂ (RegisterBasis D)) (hψ : ‖ψ‖ = 1)
    {e : ℕ} (σ : Matrix (RegisterBasis D × Fin e) (RegisterBasis D × Fin e) ℂ)
    (hσ : IsDensityMatrix σ) (hf : forgetEnvironment σ = pureDensity ψ) :
    conditionalMultipartiteInformation .total σ (singleParties m) ∅ =
      conditionalMultipartiteInformation .dual σ (singleParties m) ∅ := by
  classical
  obtain ⟨τ, hτ, hprod⟩ := ext_prod ψ hψ σ hσ.1 hf
  have hE := ent_compl (fun x => ψ x) τ hτ σ hprod
  have h1 : ∀ i : Fin m, (Finset.univ.erase i).biUnion (singleParties m) = {i}ᶜ := by
    intro i; ext j; simp [singleParties, eq_comm]
  have h2 : allParties (singleParties m) = (∅ : Finset (Fin m))ᶜ := by
    ext j; simp [allParties, singleParties]
  simp only [conditionalMultipartiteInformation, Finset.union_empty, h1, h2]
  simp only [singleParties]
  rw [← hE ∅, Finset.sum_congr rfl fun i _ => (hE {i}).symm]
  ring

end

end X4QS

end

-- ===== ERB =====

/-! Qubit erasure on one pure input with an arbitrary reference: closed forms for the output,
its marginals and their entropies. -/

noncomputable section

namespace X4EB
open Matrix Real QAlgorithms
open scoped Matrix ComplexConjugate ComplexOrder Kronecker
open QAlgorithms.Papers.Independent.Dependency50.P41 (qubitErasure)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {r : ℕ}

lemma pd_psd {ι : Type*} [Fintype ι] (v : EuclideanSpace ℂ ι) : (pureDensity v).PosSemidef := by
  have : pureDensity v = vecMulVec (WithLp.ofLp v) (star (WithLp.ofLp v)) := by
    ext a b; simp [pureDensity, vecMulVec_apply]
  rw [this]; exact Matrix.posSemidef_vecMulVec_self_star _

/-- embedded input amplitudes. -/
def phi (ψ : EuclideanSpace ℂ (Fin r × Fin 2)) : EuclideanSpace ℂ (Fin r × Fin 3) :=
  WithLp.toLp 2 fun p => if h : p.2.val < 2 then ψ (p.1, ⟨p.2.val, h⟩) else 0

/-- the reference marginal. -/
def rhoR (ψ : EuclideanSpace ℂ (Fin r × Fin 2)) : Matrix (Fin r) (Fin r) ℂ :=
  traceRight (pureDensity ψ)

/-- the flag projector `|2⟩⟨2|`. -/
def e2 : Matrix (Fin 3) (Fin 3) ℂ := pureDensity (EuclideanSpace.single (2 : Fin 3) (1 : ℂ))

/-- embedding `Fin 2 → Fin 3`. -/
def J : Matrix (Fin 3) (Fin 2) ℂ := Matrix.of fun x a => if x.val = a.val then 1 else 0

lemma J_iso : Jᴴ * J = 1 := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [J, Matrix.mul_apply, Fin.sum_univ_three]

lemma out_apply (ε : ℝ) (ψ : EuclideanSpace ℂ (Fin r × Fin 2)) (i j : Fin r) (x y : Fin 3) :
    idTensorSuperop (qubitErasure ε) (pureDensity ψ) (i, x) (j, y) =
      (1 - ε : ℂ) * phi ψ (i, x) * conj (phi ψ (j, y)) +
        (if x = 2 ∧ y = 2 then (ε : ℂ) * rhoR ψ i j else 0) := by
  fin_cases x <;> fin_cases y <;>
    simp [idTensorSuperop, qubitErasure,
      QAlgorithms.Papers.Independent.Information100.P58.singleErasure, phi, rhoR, traceRight,
      pureDensity, Matrix.trace, Fin.sum_univ_two] <;> ring

lemma out_eq (ε : ℝ) (ψ : EuclideanSpace ℂ (Fin r × Fin 2)) :
    idTensorSuperop (qubitErasure ε) (pureDensity ψ) =
      ((1 - ε : ℝ) : ℂ) • pureDensity (phi ψ) + (ε : ℂ) • (rhoR ψ ⊗ₖ e2) := by
  ext ⟨i, x⟩ ⟨j, y⟩
  rw [out_apply]
  fin_cases x <;> fin_cases y <;> simp [pureDensity, e2, kroneckerMap_apply, mul_assoc]

lemma rhoR_psd (ψ : EuclideanSpace ℂ (Fin r × Fin 2)) : (rhoR ψ).PosSemidef := by
  have : rhoR ψ = (Matrix.of fun i a => ψ (i, a)) * (Matrix.of fun i a => ψ (i, a))ᴴ := by
    ext i j; simp [rhoR, traceRight, pureDensity, Matrix.mul_apply, conjTranspose_apply]
  rw [this]; exact posSemidef_self_mul_conjTranspose _

lemma rhoR_trace (ψ : EuclideanSpace ℂ (Fin r × Fin 2)) (hψ : ‖ψ‖ = 1) : (rhoR ψ).trace = 1 := by
  have h := X4ZE.unit_sum ψ hψ
  rw [← h]
  simp [rhoR, traceRight, pureDensity, Matrix.trace, Fintype.sum_prod_type]

lemma phi_norm (ψ : EuclideanSpace ℂ (Fin r × Fin 2)) (hψ : ‖ψ‖ = 1) : ‖phi ψ‖ = 1 := by
  have h : ‖phi ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [phi, Fin.sum_univ_three, Fin.sum_univ_two]
  rw [hψ, one_pow] at h
  have := norm_nonneg (phi ψ)
  nlinarith

lemma e2_psd : e2.PosSemidef := pd_psd _

/-- binary entropy (bits) written with `logb`. -/
def hb (ε : ℝ) : ℝ := -((1 - ε) * Real.logb 2 (1 - ε)) - ε * Real.logb 2 ε

lemma smul_psd {ι : Type*} [Fintype ι] {X : Matrix ι ι ℂ} (hX : X.PosSemidef) {c : ℝ} (hc : 0 ≤ c) :
    ((c : ℂ) • X).PosSemidef := hX.smul (by exact_mod_cast hc)

lemma pd_trace {ι : Type*} [Fintype ι] (v : EuclideanSpace ℂ ι) (hv : ‖v‖ = 1) :
    (pureDensity v).trace = 1 := by
  rw [← X4ZE.unit_sum v hv]; simp [pureDensity, Matrix.trace]

lemma e2_trace : e2.trace = 1 := pd_trace _ (by simp)

lemma e2_ent : vnEntropy e2 = 0 := X4ER.vn_pure _ (by simp)

lemma ent_out (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (ψ : EuclideanSpace ℂ (Fin r × Fin 2)) (hψ : ‖ψ‖ = 1) :
    vnEntropy (idTensorSuperop (qubitErasure ε) (pureDensity ψ)) = hb ε + ε * vnEntropy (rhoR ψ) := by
  rw [out_eq]
  have hA := pd_psd (phi ψ)
  have hB : (rhoR ψ ⊗ₖ e2).PosSemidef := (rhoR_psd ψ).kronecker e2_psd
  have hAB : pureDensity (phi ψ) * (rhoR ψ ⊗ₖ e2) = 0 := by
    ext ⟨i, x⟩ ⟨j, y⟩
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_three, e2, pureDensity, phi,
      kroneckerMap_apply]
  rw [X4ER.vn_add_orth (smul_psd hA (by linarith)) (smul_psd hB h0)
    (by rw [Matrix.smul_mul, Matrix.mul_smul, hAB, smul_zero, smul_zero]),
    X4ER.vn_smul0 hA.1 (by linarith), X4ER.vn_smul0 hB.1 h0, X4ER.vn_pure _ (phi_norm ψ hψ),
    pd_trace _ (phi_norm ψ hψ), X4QS.vn_kron (rhoR_psd ψ) e2_psd, e2_ent, e2_trace, Matrix.trace_kronecker,
    rhoR_trace ψ hψ, e2_trace]
  simp [hb]; ring

lemma tl_out (ε : ℝ) (ψ : EuclideanSpace ℂ (Fin r × Fin 2)) (hψ : ‖ψ‖ = 1) :
    traceLeft (idTensorSuperop (qubitErasure ε) (pureDensity ψ)) =
      ((1 - ε : ℝ) : ℂ) • (J * traceLeft (pureDensity ψ) * Jᴴ) + (ε : ℂ) • e2 := by
  have htr' : ∑ i, rhoR ψ i i = 1 := rhoR_trace ψ hψ
  ext x y
  simp only [traceLeft, Matrix.of_apply, out_apply]
  fin_cases x <;> fin_cases y <;>
    simp [phi, J, e2, pureDensity, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three,
      conjTranspose_apply, Finset.sum_add_distrib] <;>
    (try rw [← Finset.mul_sum, htr', mul_one]) <;> simp [Finset.mul_sum] <;> ring_nf

lemma tr_out (ε : ℝ) (ψ : EuclideanSpace ℂ (Fin r × Fin 2)) :
    traceRight (idTensorSuperop (qubitErasure ε) (pureDensity ψ)) = rhoR ψ := by
  ext i j
  simp only [traceRight, Matrix.of_apply, out_apply, Fin.sum_univ_three]
  simp [phi, rhoR, traceRight, pureDensity, Fin.sum_univ_two]
  ring

lemma ent_RA (ψ : EuclideanSpace ℂ (Fin r × Fin 2)) :
    vnEntropy (rhoR ψ) = vnEntropy (traceLeft (pureDensity ψ)) := by
  set M : Matrix (Fin r) (Fin 2) ℂ := Matrix.of fun i a => ψ (i, a)
  have e1 : rhoR ψ = M * Mᴴ := by
    ext; simp [rhoR, traceRight, pureDensity, M, Matrix.mul_apply, conjTranspose_apply]
  have e2' : traceLeft (pureDensity ψ) = (Mᴴ * M)ᵀ := by
    ext; simp [traceLeft, pureDensity, M, Matrix.mul_apply, conjTranspose_apply, mul_comm]
  rw [e1, e2', X4KF.x4_ent_swap]

lemma ent_flag (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {Z : Matrix (Fin 2) (Fin 2) ℂ} (hZ : Z.PosSemidef)
    (htr : Z.trace = 1) :
    vnEntropy (((1 - ε : ℝ) : ℂ) • (J * Z * Jᴴ) + (ε : ℂ) • e2) = (1 - ε) * vnEntropy Z + hb ε := by
  have hA : (J * Z * Jᴴ).PosSemidef := hZ.mul_mul_conjTranspose_same J
  have hAB : J * Z * Jᴴ * e2 = 0 := by
    ext x y
    fin_cases x <;> fin_cases y <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, J, e2, pureDensity,
        conjTranspose_apply]
  have htrA : (J * Z * Jᴴ).trace = 1 := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, J_iso, Matrix.one_mul, htr]
  rw [X4ER.vn_add_orth (smul_psd hA (by linarith)) (smul_psd e2_psd h0)
    (by rw [Matrix.smul_mul, Matrix.mul_smul, hAB, smul_zero, smul_zero]),
    X4ER.vn_smul0 hA.1 (by linarith), X4ER.vn_smul0 e2_psd.1 h0, X4ER.vn_conj_iso hZ J J_iso,
    e2_ent, htrA, e2_trace]
  simp [hb]; ring

end X4EB

end

-- ===== ERC =====

/-! The dynamic score of the qubit erasure channel on an arbitrary pure ensemble:
`(1+μ)(1-ε) S(Z̄) + coeff · Σ p_x S(Z_x)`. -/

noncomputable section

namespace X4EC
open Matrix Real QAlgorithms X4EB
open scoped Matrix ComplexConjugate ComplexOrder Kronecker
open QAlgorithms.Papers.Independent.Claimed50.P20
open QAlgorithms.Papers.Independent.Dependency50.P41 (qubitErasure)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- input marginals. -/
def Z (e : DynamicPureEnsemble (Fin 2)) (x : Fin e.ensemble.size) : Matrix (Fin 2) (Fin 2) ℂ :=
  traceLeft (pureDensity (e.ensemble.vector x))

/-- average input marginal. -/
def Zbar (e : DynamicPureEnsemble (Fin 2)) : Matrix (Fin 2) (Fin 2) ℂ :=
  ∑ x, e.ensemble.prob x • Z e x

lemma Z_psd (e : DynamicPureEnsemble (Fin 2)) (x : Fin e.ensemble.size) : (Z e x).PosSemidef := by
  have : Z e x = (Matrix.of fun a i => (e.ensemble.vector x) (i, a)) *
      (Matrix.of fun a i => (e.ensemble.vector x) (i, a))ᴴ := by
    ext a b; simp [Z, traceLeft, pureDensity, Matrix.mul_apply, conjTranspose_apply]
  rw [this]; exact posSemidef_self_mul_conjTranspose _

lemma Z_trace (e : DynamicPureEnsemble (Fin 2)) (x : Fin e.ensemble.size) : (Z e x).trace = 1 := by
  rw [Z, X4LE.tl_trace, e.ensemble.normalized x]; simp

lemma Zbar_psd (e : DynamicPureEnsemble (Fin 2)) : (Zbar e).PosSemidef := by
  refine posSemidef_sum _ fun x _ => ?_
  rw [← Complex.coe_smul]; exact smul_psd (Z_psd e x) (e.ensemble.nonneg x)

lemma Zbar_trace (e : DynamicPureEnsemble (Fin 2)) : (Zbar e).trace = 1 := by
  rw [Zbar, Matrix.trace_sum]
  simp only [Matrix.trace_smul, Z_trace]
  have := e.ensemble.total
  rw [← Complex.ofReal_inj] at this
  push_cast at this
  simpa [Complex.real_smul] using this

lemma avg (ε : ℝ) (e : DynamicPureEnsemble (Fin 2)) :
    ∑ x, e.ensemble.prob x • traceLeft (pureOutputs (qubitErasure ε) e x) =
      ((1 - ε : ℝ) : ℂ) • (X4EB.J * Zbar e * X4EB.Jᴴ) + (ε : ℂ) • X4EB.e2 := by
  simp only [pureOutputs]
  rw [Finset.sum_congr rfl fun x _ => by
    rw [tl_out ε _ (e.ensemble.normalized x)]]
  simp only [smul_add, Finset.sum_add_distrib]
  congr 1
  · rw [Zbar, Matrix.mul_sum, Matrix.sum_mul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_comm]; rfl
  · rw [← Finset.sum_smul, e.ensemble.total, one_smul]

theorem score (ε lam mu : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (e : DynamicPureEnsemble (Fin 2)) :
    dynamicScore (qubitErasure ε) lam mu e =
      (1 + mu) * (1 - ε) * vnEntropy (Zbar e) +
        erasureCoefficient ε lam mu * ∑ x, e.ensemble.prob x * vnEntropy (Z e x) := by
  have hA : vnEntropy (∑ x, e.ensemble.prob x • traceLeft (pureOutputs (qubitErasure ε) e x)) =
      (1 - ε) * vnEntropy (Zbar e) + hb ε := by
    rw [avg, ent_flag ε h0 h1 (Zbar_psd e) (Zbar_trace e)]
  have hL : ∀ x, vnEntropy (traceLeft (pureOutputs (qubitErasure ε) e x)) =
      (1 - ε) * vnEntropy (Z e x) + hb ε := by
    intro x
    rw [pureOutputs, tl_out ε _ (e.ensemble.normalized x)]
    exact ent_flag ε h0 h1 (Z_psd e x) (Z_trace e x)
  have hR : ∀ x, vnEntropy (traceRight (pureOutputs (qubitErasure ε) e x)) = vnEntropy (Z e x) := by
    intro x; rw [pureOutputs, tr_out, ent_RA]; rfl
  have hO : ∀ x, vnEntropy (pureOutputs (qubitErasure ε) e x) = hb ε + ε * vnEntropy (Z e x) := by
    intro x; rw [pureOutputs, ent_out ε h0 h1 _ (e.ensemble.normalized x), ent_RA]; rfl
  have htot := e.ensemble.total
  simp only [dynamicScore, bounds, jointMutual, conditionalCoherent, cqHolevoBits,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, hA, hL, hR, hO, erasureCoefficient]
  set S := ∑ x, e.ensemble.prob x * vnEntropy (Z e x)
  have e1 : ∑ x, e.ensemble.prob x * (vnEntropy (Z e x) - (hb ε + ε * vnEntropy (Z e x))) =
      (1 - ε) * S - hb ε := by
    rw [show (∑ x, e.ensemble.prob x * (vnEntropy (Z e x) - (hb ε + ε * vnEntropy (Z e x)))) =
        (1 - ε) * S - hb ε * ∑ x, e.ensemble.prob x by
      simp only [S, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring, htot, mul_one]
  have f2 : ∑ x, e.ensemble.prob x * ((1 - ε) * vnEntropy (Z e x) + hb ε - (hb ε + ε * vnEntropy (Z e x))) =
      (1 - 2 * ε) * S := by
    simp only [S, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => by ring
  have e3 : ∑ x, e.ensemble.prob x * ((1 - ε) * vnEntropy (Z e x) + hb ε) = (1 - ε) * S + hb ε := by
    rw [show (∑ x, e.ensemble.prob x * ((1 - ε) * vnEntropy (Z e x) + hb ε)) =
        (1 - ε) * S + hb ε * ∑ x, e.ensemble.prob x by
      simp only [S, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring, htot, mul_one]
  rw [e1, f2, e3]
  ring

end X4EC

end

-- ===== ERD =====

noncomputable section

open Matrix Real QAlgorithms X4EB X4EC
open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms.Papers.Independent.Claimed50.P20
open QAlgorithms.Papers.Independent.Dependency50.P41 (qubitErasure)

attribute [local instance] Classical.propDecidable Classical.decEq

namespace X4ES

lemma ent_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] {X : Matrix ι ι ℂ} (hX : X.PosSemidef)
    (htr : X.trace = 1) : 0 ≤ vnEntropy X := by
  rw [X4LE.vn_amp hX, neg_nonneg]
  have hs : ∑ k, hX.1.eigenvalues k = 1 := by
    have := hX.1.trace_eq_sum_eigenvalues
    rw [htr] at this
    have h2 := congrArg Complex.re this
    simpa using h2.symm
  refine Finset.sum_nonpos fun k _ => ?_
  have h0 := hX.eigenvalues_nonneg k
  have h1 : hX.1.eigenvalues k ≤ 1 := by
    rw [← hs]
    exact Finset.single_le_sum (fun j _ => hX.eigenvalues_nonneg j) (Finset.mem_univ k)
  exact mul_nonpos_of_nonneg_of_nonpos h0 (Real.logb_nonpos (by norm_num) h0 h1)

/-- the classical witness ensemble `{|0⟩, |1⟩}` with weights `1/2`. -/
def wit : DynamicPureEnsemble (Fin 2) where
  referenceDim := 1
  referencePositive := Nat.one_pos
  ensemble :=
    { size := 2
      prob := fun _ => 1 / 2
      vector := fun x => EuclideanSpace.single ((0 : Fin 1), (⟨x.val, x.isLt⟩ : Fin 2)) 1
      nonneg := fun _ => by norm_num
      total := by norm_num
      normalized := fun _ => by simp }

lemma wit_Z (x : Fin wit.ensemble.size) :
    Z wit x = diagonal fun b => ((if b.val = x.val then 1 else 0 : ℝ) : ℂ) := by
  obtain ⟨xv, hx⟩ := x
  change xv < 2 at hx
  ext a b
  interval_cases xv <;> fin_cases a <;> fin_cases b <;>
    simp [Z, traceLeft, pureDensity, wit, PiLp.single_apply, diagonal] <;>
    erw [Fin.sum_univ_one] <;> (try simp) <;> erw [Matrix.of_apply] <;> simp

lemma wit_ent (x : Fin wit.ensemble.size) : vnEntropy (Z wit x) = 0 := by
  rw [wit_Z, X4LE.vn_diag]
  simp only [Fin.sum_univ_two]
  split_ifs <;> simp

lemma wit_bar : vnEntropy (Zbar wit) = 1 := by
  have : Zbar wit = diagonal fun _ => ((1 / 2 : ℝ) : ℂ) := by
    simp only [Zbar, wit_Z]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.sum_apply, diagonal, wit] <;> erw [Fin.sum_univ_two] <;> norm_num
  rw [this, X4LE.vn_diag, Fin.sum_univ_two]
  rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.logb_inv, Real.logb_self_eq_one (by norm_num)]
  ring

lemma wit_score (ε lam mu : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    dynamicScore (qubitErasure ε) lam mu wit = (1 + mu) * (1 - ε) := by
  rw [score ε lam mu h0 h1, wit_bar]
  simp [wit_ent]

lemma score_le (ε lam mu : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (hmu : 0 ≤ mu)
    (hc : erasureCoefficient ε lam mu ≤ 0) (e : DynamicPureEnsemble (Fin 2)) :
    dynamicScore (qubitErasure ε) lam mu e ≤ (1 + mu) * (1 - ε) := by
  rw [score ε lam mu h0 h1]
  have hS := X4ER.qubit_le (Zbar_psd e) (Zbar_trace e)
  have hT : 0 ≤ ∑ x, e.ensemble.prob x * vnEntropy (Z e x) :=
    Finset.sum_nonneg fun x _ => mul_nonneg (e.ensemble.nonneg x) (ent_nonneg (Z_psd e x) (Z_trace e x))
  have hk : 0 ≤ (1 + mu) * (1 - ε) := mul_nonneg (by linarith) (by linarith)
  nlinarith [mul_nonpos_of_nonpos_of_nonneg hc hT]

lemma escore (ε lam mu p : ℝ) :
    erasureScore ε lam mu p = (1 + mu) * (1 - ε) + erasureCoefficient ε lam mu * binEntropy2 p := by
  simp [erasureScore, erasureBounds, erasureCoefficient]; ring

lemma bin_bounds (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1 / 2) : 0 ≤ binEntropy2 p ∧ binEntropy2 p ≤ 1 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨div_nonneg (Real.binEntropy_nonneg h0 (by linarith)) hl2.le, ?_⟩
  rw [binEntropy2, div_le_one hl2]; exact Real.binEntropy_le_log_two

lemma bin_half : binEntropy2 (1 / 2) = 1 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [binEntropy2, one_div, Real.binEntropy_two_inv, div_self hl2.ne']

lemma bin_zero : binEntropy2 0 = 0 := by simp [binEntropy2]

end X4ES


end

-- ===== ERP =====

/-! Erasure dilation (`Option A` flag): receiver/complement closed forms, flag entropy,
and concavity of von Neumann entropy for probability mixtures. -/

noncomputable section

namespace X4EP
open Matrix Real QAlgorithms
open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms.Papers.Independent.Information100.P67
  (receiverChannel complementaryChannel erasureDilation)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- embedding `A → Option A`. -/
def Jo : Matrix (Option A) A ℂ := Matrix.of fun b a => if b = some a then 1 else 0

/-- the flag projector `|none⟩⟨none|`. -/
def fl : Matrix (Option A) (Option A) ℂ := pureDensity (EuclideanSpace.single (none : Option A) 1)

lemma Jo_iso : (Jo (A := A))ᴴ * Jo (A := A) = 1 := by
  ext a b
  simp [Jo, Matrix.mul_apply, Fintype.sum_option, conjTranspose_apply, Matrix.one_apply, eq_comm]

lemma fl_psd : (fl : Matrix (Option A) (Option A) ℂ).PosSemidef := X4EB.pd_psd _
lemma fl_trace : (fl : Matrix (Option A) (Option A) ℂ).trace = 1 := X4EB.pd_trace _ (by simp)
lemma fl_ent : vnEntropy (fl : Matrix (Option A) (Option A) ℂ) = 0 := X4ER.vn_pure _ (by simp)

lemma sq_c {c : ℝ} (h : 0 ≤ c) : ((Real.sqrt c : ℝ) : ℂ) * ((Real.sqrt c : ℝ) : ℂ) = (c : ℂ) := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt h]

lemma rec_eq (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (σ : Matrix A A ℂ) :
    receiverChannel (erasureDilation (A := A) ε) σ =
      ((1 - ε : ℝ) : ℂ) • (Jo (A := A) * σ * (Jo (A := A))ᴴ) + ((ε : ℝ) : ℂ) • (σ.trace • fl) := by
  have hs1 := sq_c (show 0 ≤ 1 - ε by linarith)
  have hs2 := sq_c h0
  ext b b'
  rcases b with _ | a <;> rcases b' with _ | a' <;>
    simp [receiverChannel, traceRight, erasureDilation, Matrix.mul_apply, Fintype.sum_option,
      conjTranspose_apply, Jo, fl, pureDensity, Matrix.trace, apply_ite (starRingEnd ℂ), mul_ite,
      Finset.sum_ite_eq, Finset.sum_ite_eq']
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    linear_combination σ x x * hs2
  · push_cast at hs1
    linear_combination σ a a' * hs1

lemma comp_eq (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (σ : Matrix A A ℂ) :
    complementaryChannel (erasureDilation (A := A) ε) σ =
      ((ε : ℝ) : ℂ) • (Jo (A := A) * σ * (Jo (A := A))ᴴ) + ((1 - ε : ℝ) : ℂ) • (σ.trace • fl) := by
  have hs1 := sq_c (show 0 ≤ 1 - ε by linarith)
  have hs2 := sq_c h0
  ext b b'
  rcases b with _ | a <;> rcases b' with _ | a' <;>
    simp [complementaryChannel, traceLeft, erasureDilation, Matrix.mul_apply, Fintype.sum_option,
      conjTranspose_apply, Jo, fl, pureDensity, Matrix.trace, apply_ite (starRingEnd ℂ), mul_ite,
      Finset.sum_ite_eq, Finset.sum_ite_eq']
  · push_cast at hs1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    linear_combination σ x x * hs1
  · linear_combination σ a a' * hs2

/-- entropy of a flagged mixture `a·X ⊕ b·|none⟩⟨none|` for a density `X`. -/
lemma flag_ent {X : Matrix A A ℂ} (hX : X.PosSemidef) (htr : X.trace = 1) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    vnEntropy ((a : ℂ) • (Jo (A := A) * X * (Jo (A := A))ᴴ) + (b : ℂ) • ((1 : ℂ) • fl)) =
      a * vnEntropy X - a * Real.logb 2 a - b * Real.logb 2 b := by
  rw [one_smul]
  have hJ : (Jo (A := A) * X * (Jo (A := A))ᴴ).PosSemidef := hX.mul_mul_conjTranspose_same _
  have hAB : Jo (A := A) * X * (Jo (A := A))ᴴ * fl = 0 := by
    ext u v
    simp [Matrix.mul_apply, Fintype.sum_option, Jo, fl, pureDensity, conjTranspose_apply]
  have htrJ : (Jo (A := A) * X * (Jo (A := A))ᴴ).trace = 1 := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Jo_iso, Matrix.one_mul, htr]
  rw [X4ER.vn_add_orth (X4EB.smul_psd hJ ha) (X4EB.smul_psd fl_psd hb)
    (by rw [Matrix.smul_mul, Matrix.mul_smul, hAB, smul_zero, smul_zero]),
    X4ER.vn_smul0 hJ.1 ha, X4ER.vn_smul0 fl_psd.1 hb, X4ER.vn_conj_iso hX _ Jo_iso, fl_ent,
    htrJ, fl_trace]
  simp; ring

/-- concavity of entropy for probability mixtures of densities. -/
lemma concave {ι M : Type*} [Fintype ι] [DecidableEq ι] [Fintype M] [DecidableEq M]
    (q : M → ℝ) (τ : M → Matrix ι ι ℂ) (hq : ∀ m, 0 ≤ q m) (hs : ∑ m, q m = 1)
    (hτ : ∀ m, (τ m).PosSemidef) (ht : ∀ m, (τ m).trace = 1) :
    ∑ m, q m * vnEntropy (τ m) ≤ vnEntropy (∑ m, ((q m : ℝ) : ℂ) • τ m) := by
  have h := X4LE.conc (fun m => ((q m : ℝ) : ℂ) • τ m) (fun m => X4EB.smul_psd (hτ m) (hq m))
    (by simp [Matrix.trace_smul, ht, ← Complex.ofReal_sum, hs])
  refine le_trans (le_of_eq ?_) h
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [X4ER.vn_smul0 (hτ m).1 (hq m), Matrix.trace_smul, ht m]
  simp

end X4EP

end

-- ===== PEA =====

/-! Concavity of conditional entropy (both conditionings) from strong subadditivity. -/

noncomputable section

namespace X4PE
open Matrix Real QAlgorithms
open scoped Matrix ComplexConjugate ComplexOrder

lemma vn_inst {ι : Type*} [Fintype ι] (d1 d2 : DecidableEq ι) (X : Matrix ι ι ℂ) :
    @vnEntropy ι _ d1 X = @vnEntropy ι _ d2 X := by
  congr

/-- entropy is invariant under relabelling the basis. -/
lemma vn_reindex {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : κ ≃ ι) {X : Matrix ι ι ℂ} (hX : X.PosSemidef) :
    vnEntropy (X.submatrix e e) = vnEntropy X := by
  set V : Matrix ι ι ℂ := Matrix.of fun a k => X4LE.amp hX k a
  have hV : X = V * Vᴴ := by
    conv_lhs => rw [X4LE.amp_decomp hX]
    ext a b; simp [V, Matrix.mul_apply, Matrix.sum_apply, conjTranspose_apply]
  set W : Matrix κ ι ℂ := V.submatrix e id
  have hW : X.submatrix e e = W * Wᴴ := by
    rw [hV]; ext a b; simp [W, Matrix.mul_apply, conjTranspose_apply]
  have hWW : Wᴴ * W = Vᴴ * V := by
    ext a b; simp only [W, Matrix.mul_apply, conjTranspose_apply, submatrix_apply, id]
    exact Equiv.sum_comp e (fun i => star (V i a) * V i b)
  rw [hW, X4KF.x4_ent_swap, hWW, ← X4KF.x4_ent_swap, ← hV]

open QAlgorithms.Papers.Independent.Gap48.P20 in
lemma rm_apply {X K F : Type*} [Fintype X] [Fintype K] [Fintype F]
    (ρ : Matrix X X ℂ) (keep : X → K) (forget : X → F) (e : X ≃ K × F)
    (he : ∀ x, e x = (keep x, forget x)) (a b : K) :
    redistributionMarginal ρ keep forget a b = ∑ f, ρ (e.symm (a, f)) (e.symm (b, f)) := by
  classical
  unfold redistributionMarginal
  have hk : ∀ u, keep (e.symm u) = u.1 := fun u => by
    have := he (e.symm u); rw [Equiv.apply_symm_apply] at this; exact (congrArg Prod.fst this).symm
  have hf : ∀ u, forget (e.symm u) = u.2 := fun u => by
    have := he (e.symm u); rw [Equiv.apply_symm_apply] at this; exact (congrArg Prod.snd this).symm
  rw [← e.symm.sum_comp]
  simp_rw [← e.symm.sum_comp (fun y => if _ then _ else _), hk, hf]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a]
  · refine Finset.sum_congr rfl fun f _ => ?_
    rw [Fintype.sum_prod_type, Finset.sum_eq_single b]
    · rw [Finset.sum_eq_single f]
      · simp
      · intro g _ hg; rw [if_neg]; intro h; exact hg h.2.2.symm
      · simp
    · intro k _ hk'; refine Finset.sum_eq_zero fun g _ => ?_
      rw [if_neg]; intro h; exact hk' h.2.1
    · simp
  · intro k _ hk'; refine Finset.sum_eq_zero fun f _ => Finset.sum_eq_zero fun v _ => ?_
    rw [if_neg]; intro h; exact hk' h.1
  · simp


section
variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

def KL (a : A) : Matrix B (A × B) ℂ := Matrix.of fun b p => if p = (a, b) then 1 else 0
def KR (b : B) : Matrix A (A × B) ℂ := Matrix.of fun a p => if p = (a, b) then 1 else 0

lemma tl_kraus (ω : Matrix (A × B) (A × B) ℂ) : traceLeft ω = ∑ a, (KL (B := B) a : Matrix B (A × B) ℂ) * ω * (KL (B := B) a : Matrix B (A × B) ℂ)ᴴ := by
  ext b b'
  simp [traceLeft, KL, Matrix.mul_apply, Matrix.sum_apply, conjTranspose_apply]

lemma tr_kraus (ω : Matrix (A × B) (A × B) ℂ) : traceRight ω = ∑ b, (KR (A := A) b : Matrix A (A × B) ℂ) * ω * (KR (A := A) b : Matrix A (A × B) ℂ)ᴴ := by
  ext a a'
  simp [traceRight, KR, Matrix.mul_apply, Matrix.sum_apply, conjTranspose_apply]

lemma tl_psd {ω : Matrix (A × B) (A × B) ℂ} (h : ω.PosSemidef) : (traceLeft ω).PosSemidef := by
  rw [tl_kraus]; exact Matrix.posSemidef_sum _ fun a _ => h.mul_mul_conjTranspose_same _

lemma tr_psd {ω : Matrix (A × B) (A × B) ℂ} (h : ω.PosSemidef) : (traceRight ω).PosSemidef := by
  rw [tr_kraus]; exact Matrix.posSemidef_sum _ fun a _ => h.mul_mul_conjTranspose_same _

lemma tl_trace (ω : Matrix (A × B) (A × B) ℂ) : (traceLeft ω).trace = ω.trace := by
  simp only [Matrix.trace, traceLeft, Matrix.diag, Matrix.of_apply]
  rw [Finset.sum_comm, ← Fintype.sum_prod_type']

lemma tr_trace (ω : Matrix (A × B) (A × B) ℂ) : (traceRight ω).trace = ω.trace := by
  simp only [Matrix.trace, traceRight, Matrix.diag, Matrix.of_apply]
  rw [← Fintype.sum_prod_type']

lemma tl_smul (c : ℂ) (ω : Matrix (A × B) (A × B) ℂ) : traceLeft (c • ω) = c • traceLeft ω := by
  ext; simp [traceLeft, Finset.mul_sum]

lemma tl_sum {M : Type*} [Fintype M] (ω : M → Matrix (A × B) (A × B) ℂ) :
    traceLeft (∑ m, ω m) = ∑ m, traceLeft (ω m) := by
  ext; simp [traceLeft, Matrix.sum_apply]; rw [Finset.sum_comm]

end

def e1 (M R B : Type*) : M × (R × B) ≃ (M × B) × R where
  toFun p := ((p.1, p.2.2), p.2.1)
  invFun u := (u.1.1, (u.2, u.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

def e3 (M R B : Type*) : M × (R × B) ≃ B × (M × R) where
  toFun p := (p.2.2, (p.1, p.2.1))
  invFun u := (u.2.1, (u.2.2, u.1))
  left_inv _ := rfl
  right_inv _ := rfl

section
variable {M R B : Type*} [Fintype M] [DecidableEq M] [Nonempty M] [Fintype R] [DecidableEq R]
  [Nonempty R] [Fintype B] [DecidableEq B] [Nonempty B]

open QAlgorithms.Papers.Independent.Gap48.P20 in
/-- concavity of `H(R|B)`. -/
theorem condR (q : M → ℝ) (θ : M → Matrix (R × B) (R × B) ℂ) (hq : ∀ m, 0 ≤ q m)
    (hs : ∑ m, q m = 1) (hθ : ∀ m, (θ m).PosSemidef) (ht : ∀ m, (θ m).trace = 1) :
    ∑ m, q m * (vnEntropy (θ m) - vnEntropy (traceLeft (θ m))) ≤
      vnEntropy (∑ m, ((q m : ℝ) : ℂ) • θ m) - vnEntropy (traceLeft (∑ m, ((q m : ℝ) : ℂ) • θ m)) := by
  set σ : M → Matrix (R × B) (R × B) ℂ := fun m => ((q m : ℝ) : ℂ) • θ m with hσdef
  have hσ : ∀ m, (σ m).PosSemidef := fun m => X4EB.smul_psd (hθ m) (hq m)
  set ω := X4LE.blk σ
  have hpsd : ω.PosSemidef := by
    show (X4LE.blk σ).PosSemidef
    rw [X4LE.blk_decomp σ hσ]
    refine Matrix.posSemidef_sum _ fun t _ => ?_
    have := Matrix.posSemidef_vecMulVec_self_star (fun x : M × (R × B) =>
      if x.1 = t.1 then X4LE.amp (hσ t.1) t.2 x.2 else 0)
    convert this using 1
    ext x y; simp [vecMulVec_apply]
  have htr : ω.trace = 1 := by
    rw [Matrix.trace, Fintype.sum_prod_type]
    simp only [ω, X4LE.blk, Matrix.diag, if_true]
    simp only [σ, Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    have : ∀ m, ∑ i, θ m i i = 1 := fun m => ht m
    simp only [this, mul_one]; exact_mod_cast hs
  have h := strongSubadditivity ω ⟨hpsd, htr⟩
  have m1 : redistributionMarginal ω (fun p => (p.1, p.2.2)) (fun p => p.2.1) =
      X4LE.blk (fun m => traceLeft (σ m)) := by
    ext ⟨c, b⟩ ⟨c', b'⟩
    rw [rm_apply _ _ _ (e1 M R B) (fun _ => rfl)]
    simp only [e1, Equiv.coe_fn_symm_mk, ω, X4LE.blk, traceLeft, Matrix.of_apply]
    split_ifs <;> simp
  have m2 : redistributionMarginal ω (fun p => p.2) (fun p => p.1) = ∑ m, σ m := by
    ext x x'
    rw [rm_apply _ _ _ (Equiv.prodComm M (R × B)) (fun _ => rfl)]
    simp [ω, X4LE.blk, Matrix.sum_apply]
  have m3 : redistributionMarginal ω (fun p => p.2.2) (fun p => (p.1, p.2.1)) =
      traceLeft (∑ m, σ m) := by
    ext b b'
    rw [rm_apply _ _ _ (e3 M R B) (fun _ => rfl)]
    simp [e3, ω, X4LE.blk, traceLeft, Matrix.sum_apply, Fintype.sum_prod_type]
    exact Finset.sum_comm
  have key : 0 ≤ vnEntropy (X4LE.blk (fun m => traceLeft (σ m))) + vnEntropy (∑ m, σ m) -
      vnEntropy (traceLeft (∑ m, σ m)) - vnEntropy ω := by
    unfold subsystemEntropy at h
    rw [m1, m2, m3] at h
    rw [vn_inst _ inferInstance (X4LE.blk fun m => traceLeft (σ m)), vn_inst _ inferInstance (∑ m, σ m),
      vn_inst _ inferInstance (traceLeft (∑ m, σ m)), vn_inst _ inferInstance ω] at h
    exact h
  rw [X4LE.vn_blk _ (fun m => tl_psd (hσ m)), X4LE.vn_blk _ hσ] at key
  have e1 : ∀ m, vnEntropy (traceLeft (σ m)) = q m * vnEntropy (traceLeft (θ m)) - q m * Real.logb 2 (q m) := by
    intro m
    rw [hσdef]; dsimp only
    rw [tl_smul, X4ER.vn_smul0 (tl_psd (hθ m)).1 (hq m), tl_trace, ht m]; simp
  have e2 : ∀ m, vnEntropy (σ m) = q m * vnEntropy (θ m) - q m * Real.logb 2 (q m) := by
    intro m
    rw [hσdef]; dsimp only
    rw [X4ER.vn_smul0 (hθ m).1 (hq m), ht m]; simp
  simp only [e1, e2] at key
  simp only [mul_sub, Finset.sum_sub_distrib] at key ⊢
  linarith

/-- concavity of `H(B|R)`. -/
theorem condL (q : M → ℝ) (θ : M → Matrix (R × B) (R × B) ℂ) (hq : ∀ m, 0 ≤ q m)
    (hs : ∑ m, q m = 1) (hθ : ∀ m, (θ m).PosSemidef) (ht : ∀ m, (θ m).trace = 1) :
    ∑ m, q m * (vnEntropy (θ m) - vnEntropy (traceRight (θ m))) ≤
      vnEntropy (∑ m, ((q m : ℝ) : ℂ) • θ m) - vnEntropy (traceRight (∑ m, ((q m : ℝ) : ℂ) • θ m)) := by
  set sw := Equiv.prodComm B R
  have h := condR q (fun m => (θ m).submatrix sw sw) hq hs
    (fun m => (hθ m).submatrix _) (fun m => by
      rw [← ht m]; simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
      exact Equiv.sum_comp sw (fun i => θ m i i))
  have etl : ∀ X : Matrix (R × B) (R × B) ℂ, traceLeft (X.submatrix sw sw) = traceRight X := by
    intro X; ext; simp [traceLeft, traceRight, sw]
  have esum : (∑ m, ((q m : ℝ) : ℂ) • (θ m).submatrix sw sw) = (∑ m, ((q m : ℝ) : ℂ) • θ m).submatrix sw sw := by
    ext; simp [Matrix.sum_apply]
  have hpsd : (∑ m, ((q m : ℝ) : ℂ) • θ m).PosSemidef :=
    Matrix.posSemidef_sum _ fun m _ => X4EB.smul_psd (hθ m) (hq m)
  simp only [etl, esum, vn_reindex sw (hθ _), vn_reindex sw hpsd] at h
  exact h

end

end X4PE


end

-- ===== DCSol =====
noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P02

open QAlgorithms.Papers.Independent.Information100.P67
  (squaredFidelity receiverChannel complementaryChannel IsDegradable)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble)

open QAlgorithms.Papers.Independent.Dependency50.P19 (epr)

attribute [local instance] Classical.propDecidable Classical.decEq


namespace X4DC
open Matrix

/-- Stinespring isometry of a Kraus family. -/
def W {E B : Type*} {m : ℕ} (K : Fin m → Matrix E B ℂ) : Matrix (E × Fin m) B ℂ :=
  Matrix.of fun p b => K p.2 p.1 b

lemma W_iso {E B : Type*} [Fintype E] [Fintype B] [DecidableEq B] {m : ℕ} (K : Fin m → Matrix E B ℂ)
    (hK : ∑ k, (K k)ᴴ * K k = 1) : (W K)ᴴ * W K = 1 := by
  rw [← hK]; ext b b'
  simp only [W, Matrix.mul_apply, conjTranspose_apply, Matrix.of_apply, Matrix.sum_apply,
    Fintype.sum_prod_type]
  exact Finset.sum_comm

lemma W_tr {E B : Type*} [Fintype E] [Fintype B] {m : ℕ} (K : Fin m → Matrix E B ℂ) (X : Matrix B B ℂ) :
    traceRight (W K * X * (W K)ᴴ) = krausApply K X := by
  ext e e'
  simp only [traceRight, krausApply, W, Matrix.mul_apply, conjTranspose_apply, Matrix.of_apply,
    Matrix.sum_apply]

end X4DC

variable {A B C E R S I J : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype E] [DecidableEq E]

variable [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]

variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Concavity in the INPUT of a degradable channel, §7.3, PDF p.35.
This is distinct from background convexity in the channel at fixed input (p.4). -/
theorem solution [Nonempty A] [Nonempty B] [Nonempty E]
    (U : Matrix (B × E) A ℂ) (hU : IsDegradable U)
    (rho0 rho1 : Op A) (h0 : IsDensityMatrix rho0) (h1 : IsDensityMatrix rho1)
    (lambda : ℝ) (hl0 : 0 ≤ lambda) (hl1 : lambda ≤ 1) :
    lambda * inputCoherent U rho0 + (1 - lambda) * inputCoherent U rho1 ≤
      inputCoherent U ((lambda : ℂ) • rho0 + ((1 - lambda : ℝ) : ℂ) • rho1) := by
  obtain ⟨hiso, D, hD, hdeg⟩ := hU
  obtain ⟨m, K, hK, hDK⟩ := hD
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      obtain ⟨b⟩ := ‹Nonempty B›
      have := congrFun (congrFun hK b) b
      simp at this
    · exact h
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hiso' : Uᴴ * U = 1 := hiso
  have hWi := X4DC.W_iso K hK
  have hσpsd : ∀ ρ : Op A, ρ.PosSemidef → (receiverChannel U ρ).PosSemidef := fun ρ hρ =>
    X4PE.tr_psd (hρ.mul_mul_conjTranspose_same U)
  have hσtr : ∀ ρ : Op A, (receiverChannel U ρ).trace = ρ.trace := fun ρ => by
    simp only [receiverChannel]
    rw [X4PE.tr_trace, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hiso', Matrix.one_mul]
  set τ : Op A → Matrix (E × Fin m) (E × Fin m) ℂ := fun ρ => X4DC.W K * receiverChannel U ρ * (X4DC.W K)ᴴ
    with hτ
  have hτpsd : ∀ ρ : Op A, ρ.PosSemidef → (τ ρ).PosSemidef := fun ρ hρ =>
    (hσpsd ρ hρ).mul_mul_conjTranspose_same _
  have hτtr : ∀ ρ : Op A, (τ ρ).trace = ρ.trace := fun ρ => by
    simp only [hτ]
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hWi, Matrix.one_mul, hσtr]
  have key : ∀ ρ : Op A, ρ.PosSemidef →
      inputCoherent U ρ = vnEntropy (τ ρ) - vnEntropy (traceRight (τ ρ)) := by
    intro ρ hρ
    unfold inputCoherent
    rw [hdeg, hDK, hτ]
    dsimp only
    rw [X4DC.W_tr, X4ER.vn_conj_iso (hσpsd ρ hρ) _ hWi]
  have hlin : τ ((lambda : ℂ) • rho0 + ((1 - lambda : ℝ) : ℂ) • rho1) =
      ∑ i : Fin 2, ((![lambda, 1 - lambda] i : ℝ) : ℂ) • ![τ rho0, τ rho1] i := by
    have hrc : ∀ (a b : ℂ) (X Y : Op A), receiverChannel U (a • X + b • Y) =
        a • receiverChannel U X + b • receiverChannel U Y := by
      intro a b X Y
      simp only [receiverChannel, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
      ext i j; simp [traceRight, Finset.sum_add_distrib, Finset.mul_sum]
    rw [Fin.sum_univ_two]
    simp only [hτ]
    rw [hrc]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
    simp
  have hmix : ((lambda : ℂ) • rho0 + ((1 - lambda : ℝ) : ℂ) • rho1).PosSemidef := by
    refine (X4EB.smul_psd h0.1 hl0).add (X4EB.smul_psd h1.1 (by linarith))
  have hc := X4PE.condL (M := Fin 2) ![lambda, 1 - lambda] ![τ rho0, τ rho1]
    (fun i => by fin_cases i <;> simp [hl0] <;> linarith)
    (by simp)
    (fun i => by fin_cases i <;> simp [hτpsd _ h0.1, hτpsd _ h1.1])
    (fun i => by fin_cases i <;> simp [hτtr, h0.2, h1.2])
  rw [key _ h0.1, key _ h1.1, key _ hmix, hlin]
  rw [Fin.sum_univ_two] at hc
  simpa using hc

