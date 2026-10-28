-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P41.dilationEnvironmentFreedom
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T00:34:40.804797+00:00
-- url     : https://prove2.me/submissions/964db404-47c7-4f20-b80d-041ffe5322f6

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

-- ===== KFSol3 =====

noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P41
open QAlgorithms.Papers.Independent.Gap20.P06 (dilationChannel environmentOutput dilatedVector)
open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq
local instance (priority := 2000) instKFSol3 (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

theorem solution {d e : ℕ} [NeZero d] [NeZero e]
    (U V : Matrix.unitaryGroup (Fin d × Fin e) ℂ)
    (eta zeta : EuclideanSpace ℂ (Fin e)) (heta : IsState eta) (hzeta : IsState zeta)
    (hsame : ∀ X, dilationChannel U eta X = dilationChannel V zeta X) :
    ∃ W : Matrix.unitaryGroup (Fin e) ℂ,
      ∀ v : EuclideanSpace ℂ (Fin d),
        act (V : Matrix (Fin d × Fin e) (Fin d × Fin e) ℂ)
          (WithLp.toLp 2 fun p => v p.1 * zeta p.2) =
        act (Matrix.kronecker (1 : Matrix (Fin d) (Fin d) ℂ)
          (W : Matrix (Fin e) (Fin e) ℂ))
          (act (U : Matrix (Fin d × Fin e) (Fin d × Fin e) ℂ)
            (WithLp.toLp 2 fun p => v p.1 * eta p.2)) :=
  X4KF.env_freedom U V eta zeta hsame

end

#print axioms solution
