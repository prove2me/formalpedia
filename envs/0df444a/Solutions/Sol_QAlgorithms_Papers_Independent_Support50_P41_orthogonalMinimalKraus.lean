-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P41.orthogonalMinimalKraus
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T00:27:27.879823+00:00
-- url     : https://prove2.me/submissions/cbf15d27-812b-4cb8-9681-54878485ba21

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

-- ===== KFB =====

noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P41
open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq
local instance (priority := 2000) instKFB (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

namespace X4KF
open Matrix

lemma sum_pad {d m L : ℕ} {M : Type*} [AddCommMonoid M] (A : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (hmL : m ≤ L) (g : Matrix (Fin d) (Fin d) ℂ → M) (hg : g 0 = 0) :
    ∑ k, g (padKraus A L k) = ∑ k, g (A k) := by
  let f : ℕ → M := fun i => if h : i < m then g (A ⟨i, h⟩) else 0
  have h1 : ∑ k : Fin L, g (padKraus A L k) = ∑ i ∈ Finset.range L, f i := by
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [padKraus, f]
    split_ifs <;> simp [hg]
  have h2 : ∑ k : Fin m, g (A k) = ∑ i ∈ Finset.range m, f i := by
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [f]
  rw [h1, h2]
  symm
  refine Finset.sum_subset (Finset.range_subset_range.mpr hmL) fun i _ hi => ?_
  simp only [Finset.mem_range, not_lt] at hi
  simp [f, show ¬ i < m by omega]

lemma kraus_pad {d m L : ℕ} (A : Fin m → Matrix (Fin d) (Fin d) ℂ) (hmL : m ≤ L) (X) :
    krausApply (padKraus A L) X = krausApply A X := by
  unfold krausApply
  exact sum_pad A hmL (fun B => B * X * Bᴴ) (by simp)

lemma entry_kraus {d L : ℕ} (A : Fin L → Matrix (Fin d) (Fin d) ℂ) (a i b j : Fin d) :
    krausApply A (Matrix.single j i 1) b a = ∑ l, conj (A l a i) * A l b j := by
  simp only [krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.single_apply,
    conjTranspose_apply, RCLike.star_def]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_eq_single i (fun x _ hx => by simp [Ne.symm hx]) (by simp),
    Finset.sum_eq_single j (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
  simp [mul_comm]

theorem freedom {d m n : ℕ} (Phi : Superop (Fin d) (Fin d))
    (A : Fin m → Matrix (Fin d) (Fin d) ℂ) (hA : OperatorSum Phi A)
    (B : Fin n → Matrix (Fin d) (Fin d) ℂ) (hB : OperatorSum Phi B) :
    ∃ U : Matrix.unitaryGroup (Fin (max m n)) ℂ,
      ∀ k : Fin (max m n), padKraus A (max m n) k =
        ∑ l, (U : Matrix (Fin (max m n)) (Fin (max m n)) ℂ) k l •
          padKraus B (max m n) l := by
  set L := max m n
  have hAB : ∀ X, krausApply (padKraus A L) X = krausApply (padKraus B L) X := by
    intro X
    rw [kraus_pad A (le_max_left m n), kraus_pad B (le_max_right m n), ← hA.2, ← hB.2]
  obtain ⟨U, hU⟩ := gram_unitary (L := L) (P := Fin d × Fin d)
    (fun p l => padKraus A L l p.1 p.2) (fun p l => padKraus B L l p.1 p.2) (by
      rintro ⟨a, i⟩ ⟨b, j⟩
      simp only
      rw [← entry_kraus, ← entry_kraus, hAB])
  refine ⟨U, fun k => ?_⟩
  ext a i
  rw [hU (a, i) k, Matrix.sum_apply]
  rfl

end X4KF

-- ===== P41DKLib =====

noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P41
open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq
local instance (priority := 2000) (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

namespace X4P41K
open Matrix

variable {d m : ℕ}

/-- unitary mixing of Kraus operators -/
def mix (V : Matrix (Fin m) (Fin m) ℂ) (E : Fin m → Matrix (Fin d) (Fin d) ℂ) (k : Fin m) :
    Matrix (Fin d) (Fin d) ℂ := ∑ l, conj (V l k) • E l

lemma mix_ct (V : Matrix (Fin m) (Fin m) ℂ) (E : Fin m → Matrix (Fin d) (Fin d) ℂ) (k : Fin m) :
    (mix V E k)ᴴ = ∑ l, V l k • (E l)ᴴ := by
  simp [mix, conjTranspose_sum, conjTranspose_smul]

lemma VVh (V : Matrix (Fin m) (Fin m) ℂ) (hV : V ∈ Matrix.unitaryGroup (Fin m) ℂ) (l l' : Fin m) :
    ∑ k, V l k * conj (V l' k) = if l = l' then 1 else 0 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.1 hV) l) l'
  simp only [Matrix.mul_apply, star_apply, RCLike.star_def, one_apply] at h
  exact h

lemma perm3 {α : Type*} [AddCommMonoid α] (f : Fin m → Fin m → Fin m → α) :
    (∑ k, ∑ l, ∑ l', f k l l') = ∑ l, ∑ l', ∑ k, f k l l' := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_comm

lemma collapse {α : Type*} [AddCommGroup α] [Module ℂ α] (V : Matrix (Fin m) (Fin m) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Fin m) ℂ) (M : Fin m → Fin m → α) :
    (∑ l, ∑ l', ∑ k, (V l k * conj (V l' k)) • M l l') = ∑ l, M l l := by
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [← Finset.sum_smul, VVh V hV, ite_smul, one_smul, zero_smul]
  rw [Finset.sum_ite_eq]; simp

lemma mix_kraus (V : Matrix (Fin m) (Fin m) ℂ) (hV : V ∈ Matrix.unitaryGroup (Fin m) ℂ)
    (E : Fin m → Matrix (Fin d) (Fin d) ℂ) (X : Matrix (Fin d) (Fin d) ℂ) :
    ∑ k, (mix V E k)ᴴ * X * mix V E k = ∑ l, (E l)ᴴ * X * E l := by
  have expand : ∀ k, (mix V E k)ᴴ * X * mix V E k =
      ∑ l, ∑ l', (V l' k * conj (V l k)) • ((E l')ᴴ * X * E l) := by
    intro k
    rw [mix_ct]
    simp only [mix, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_smul,
      Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
    rw [mul_comm (V l' k)]
  simp_rw [expand]
  rw [perm3, Finset.sum_comm, collapse V hV (fun a b => (E a)ᴴ * X * E b)]

lemma mix_act (V : Matrix (Fin m) (Fin m) ℂ) (hV : V ∈ Matrix.unitaryGroup (Fin m) ℂ)
    (E : Fin m → Matrix (Fin d) (Fin d) ℂ) (X : Matrix (Fin d) (Fin d) ℂ) :
    ∑ k, mix V E k * X * (mix V E k)ᴴ = ∑ l, E l * X * (E l)ᴴ := by
  have expand : ∀ k, mix V E k * X * (mix V E k)ᴴ =
      ∑ l, ∑ l', (V l k * conj (V l' k)) • (E l' * X * (E l)ᴴ) := by
    intro k
    rw [mix_ct]
    simp only [mix, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_smul,
      Finset.smul_sum]
  simp_rw [expand]
  rw [perm3, collapse V hV (fun l l' => E l' * X * (E l)ᴴ)]

theorem main (Phi : Superop (Fin d) (Fin d)) (hPhi : IsChannel Phi)
    (rho : Matrix (Fin d) (Fin d) ℂ) (hrho : IsDensityMatrix rho) :
    ∃ m : ℕ, ∃ A : Fin m → Matrix (Fin d) (Fin d) ℂ,
      OperatorSum Phi A ∧ ∀ k l, k ≠ l → (A k * rho * (A l)ᴴ).trace = 0 := by
  obtain ⟨m, E, hK, hE⟩ := hPhi
  let W : Matrix (Fin m) (Fin m) ℂ := Matrix.of fun k l => (E k * rho * (E l)ᴴ).trace
  have hW : W.IsHermitian := by
    ext k l
    rw [conjTranspose_apply]
    simp only [W, Matrix.of_apply]
    rw [← Matrix.trace_conjTranspose]
    congr 1
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, conjTranspose_conjTranspose,
      hrho.1.1.eq, Matrix.mul_assoc]
  set V := (hW.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)
  have hV : V ∈ Matrix.unitaryGroup (Fin m) ℂ := hW.eigenvectorUnitary.2
  have hspec := hW.spectral_theorem
  have hD : star V * W * V = diagonal (RCLike.ofReal ∘ hW.eigenvalues) := by
    conv_lhs => rw [hspec]
    simp only [Unitary.conjStarAlgAut_apply]
    have h1 : star V * V = 1 := Matrix.mem_unitaryGroup_iff'.1 hV
    simp only [V] at h1 ⊢
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc, h1,
      Matrix.mul_one]
  refine ⟨m, mix V E, ⟨?_, fun X => ?_⟩, fun k l hkl => ?_⟩
  · unfold IsKrausFamily
    have := mix_kraus V hV E 1
    simp only [Matrix.mul_one] at this
    rw [this]; exact hK
  · rw [hE X, krausApply, krausApply, mix_act V hV E X]
  · have := congrFun (congrFun hD k) l
    rw [diagonal_apply_ne _ hkl] at this
    rw [← this, mix_ct]
    simp only [mix, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
      Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, Matrix.mul_apply, star_apply,
      RCLike.star_def, W, Matrix.of_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring

end X4P41K


-- ===== KFC =====

noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P41
open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq
local instance (priority := 2000) instKFC (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

namespace X4KF
open Matrix

lemma drop_zero {d m : ℕ} {M : Type*} [AddCommMonoid M] (A : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (g : Matrix (Fin d) (Fin d) ℂ → M) (hg : g 0 = 0) :
    let S := {k // A k ≠ 0}
    ∑ j : Fin (Fintype.card S), g (A ((Fintype.equivFin S).symm j)) = ∑ k, g (A k) := by
  intro S
  rw [(Fintype.equivFin S).symm.sum_comp (fun s : S => g (A s))]
  rw [← Finset.sum_subtype (Finset.univ.filter fun k => A k ≠ 0) (by simp) (fun k => g (A k))]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs with h
  · rfl
  · push Not at h; rw [h, hg]

lemma exists_orth {d : ℕ} [NeZero d] (Phi : Superop (Fin d) (Fin d)) (hPhi : IsChannel Phi) :
    ∃ m : ℕ, ∃ A : Fin m → Matrix (Fin d) (Fin d) ℂ,
      OperatorSum Phi A ∧ (∀ k, A k ≠ 0) ∧
        ∀ k l, k ≠ l → ((A k)ᴴ * A l).trace = 0 := by
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have hrho : IsDensityMatrix (((d : ℂ)⁻¹) • (1 : Matrix (Fin d) (Fin d) ℂ)) := by
    refine ⟨?_, ?_⟩
    · refine Matrix.PosSemidef.smul Matrix.PosSemidef.one ?_
      rw [show ((d : ℂ))⁻¹ = (((d : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl]
      exact Complex.zero_le_real.mpr (by positivity)
    · rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul, inv_mul_cancel₀ hd]
  obtain ⟨m, E, hE, horth⟩ := X4P41K.main Phi hPhi _ hrho
  have hE' : ∀ k l, k ≠ l → ((E k)ᴴ * E l).trace = 0 := by
    intro k l hkl
    have := horth l k (Ne.symm hkl)
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul] at this
    rw [Matrix.trace_mul_comm]
    exact (mul_eq_zero.mp this).resolve_left (inv_ne_zero hd)
  let S := {k // E k ≠ 0}
  let e := (Fintype.equivFin S).symm
  refine ⟨Fintype.card S, fun j => E (e j), ⟨?_, fun X => ?_⟩, fun j => (e j).2, fun j j' hjj => ?_⟩
  · unfold IsKrausFamily
    rw [drop_zero E (fun B => Bᴴ * B) (by simp)]
    exact hE.1
  · rw [hE.2 X]
    unfold krausApply
    exact (drop_zero E (fun B => B * X * Bᴴ) (by simp)).symm
  · refine hE' _ _ fun h => hjj ?_
    exact e.injective (Subtype.ext h)

lemma lin_indep {d m : ℕ} (A : Fin m → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ k, A k ≠ 0)
    (horth : ∀ k l, k ≠ l → ((A k)ᴴ * A l).trace = 0) : LinearIndependent ℂ A := by
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have h1 := congrArg (fun M => ((A j)ᴴ * M).trace) hc
  simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul,
    Matrix.mul_zero, Matrix.trace_zero] at h1
  rw [Finset.sum_eq_single j (fun k _ hk => by rw [horth j k (Ne.symm hk), mul_zero])
    (by simp)] at h1
  have h2 : ((A j)ᴴ * A j).trace ≠ 0 := by
    intro h
    exact hA j (Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp h)
  exact (mul_eq_zero.mp h1).resolve_right h2

lemma minimal {d m n : ℕ} (Phi : Superop (Fin d) (Fin d))
    (A : Fin m → Matrix (Fin d) (Fin d) ℂ) (hA : OperatorSum Phi A) (hA0 : ∀ k, A k ≠ 0)
    (horth : ∀ k l, k ≠ l → ((A k)ᴴ * A l).trace = 0)
    (B : Fin n → Matrix (Fin d) (Fin d) ℂ) (hB : OperatorSum Phi B) : m ≤ n := by
  obtain ⟨U, hU⟩ := freedom Phi A hA B hB
  set L := max m n
  let W := Submodule.span ℂ (Set.range B)
  have hmem : ∀ k : Fin m, A k ∈ W := by
    intro k
    have := hU ⟨k.val, lt_of_lt_of_le k.isLt (le_max_left m n)⟩
    have hk : padKraus A L ⟨k.val, lt_of_lt_of_le k.isLt (le_max_left m n)⟩ = A k := by
      simp [padKraus]
    rw [hk] at this
    rw [this]
    refine Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ ?_
    unfold padKraus
    split_ifs
    · exact Submodule.subset_span ⟨_, rfl⟩
    · exact W.zero_mem
  let A' : Fin m → W := fun k => ⟨A k, hmem k⟩
  have hli : LinearIndependent ℂ A' := by
    apply LinearIndependent.of_comp W.subtype
    exact lin_indep A hA0 horth
  have := hli.fintype_card_le_finrank
  simp only [Fintype.card_fin] at this
  exact this.trans ((finrank_range_le_card B).trans (by simp))

end X4KF

-- ===== KFSol2 =====

noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P41
open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq
local instance (priority := 2000) instKFSol2 (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

theorem solution {d : ℕ} [NeZero d]
    (Phi : Superop (Fin d) (Fin d)) (hPhi : IsChannel Phi) :
    (∃ m : ℕ, ∃ A : Fin m → Matrix (Fin d) (Fin d) ℂ,
      OperatorSum Phi A ∧ (∀ k, A k ≠ 0) ∧
        ∀ k l, k ≠ l → ((A k)ᴴ * A l).trace = 0) ∧
    ∀ m (A : Fin m → Matrix (Fin d) (Fin d) ℂ), OperatorSum Phi A →
      (∀ k, A k ≠ 0) → (∀ k l, k ≠ l → ((A k)ᴴ * A l).trace = 0) →
      ∀ n (B : Fin n → Matrix (Fin d) (Fin d) ℂ), OperatorSum Phi B → m ≤ n :=
  ⟨X4KF.exists_orth Phi hPhi, fun _ A hA hA0 horth _ B hB => X4KF.minimal Phi A hA hA0 horth B hB⟩

end

#print axioms solution
