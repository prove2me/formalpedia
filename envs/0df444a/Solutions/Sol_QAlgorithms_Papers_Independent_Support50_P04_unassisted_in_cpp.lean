-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P04.unassisted_in_cpp
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:11:39.802747+00:00
-- url     : https://prove2.me/submissions/47fba89e-79f3-42f1-a589-b0cbc7008917

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P04

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms

namespace S176U
open QAlgorithms.Papers.Independent.Dependency50.P22
open QAlgorithms.Papers.Independent.Information100.P27 (Config)

/-- Reindexing a channel by equivalences gives a channel. -/
theorem reindex_channel {ι κ ι' κ' : Type} [Fintype ι] [Fintype κ] [DecidableEq ι]
    [Fintype ι'] [Fintype κ'] [DecidableEq ι'] [DecidableEq κ]
    (Φ : Superop ι κ) (hΦ : IsChannel Φ) (e1 : ι' ≃ ι) (e2 : κ' ≃ κ) :
    IsChannel (fun X : Matrix ι' ι' ℂ => (Φ (X.submatrix e1.symm e1.symm)).submatrix e2 e2) := by
  obtain ⟨m, E, hE, hΦE⟩ := hΦ
  refine ⟨m, fun j => (E j).submatrix e2 e1, ?_, ?_⟩
  · unfold IsKrausFamily at hE ⊢
    ext a b
    have h := congrFun (congrFun hE (e1 a)) (e1 b)
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.submatrix_apply] at h ⊢
    rw [Matrix.one_apply] at h ⊢
    simp only [e1.apply_eq_iff_eq] at h
    rw [← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact Fintype.sum_equiv e2 _ _ (fun _ => rfl)
  · intro X
    show (Φ (X.submatrix e1.symm e1.symm)).submatrix e2 e2 = _
    rw [hΦE]
    unfold krausApply
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.sum_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Equiv.sum_comp e1]
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    rw [← Equiv.sum_comp e1]
    simp

theorem cp_id {I : Type} [Fintype I] :
    Entanglement.IsCompletelyPositive (LinearMap.id : Matrix I I ℂ →ₗ[ℂ] Matrix I I ℂ) := by
  intro r X hX
  have : idTensorSuperop (R := Fin r) (⇑(LinearMap.id : Matrix I I ℂ →ₗ[ℂ] Matrix I I ℂ)) X = X := by
    ext p q; rfl
  rw [this]; exact hX

/-- The trivial instrument: outcome `0` is the identity, all other outcomes vanish. -/
def J0 (I : Type) : ℕ → Superop I I := fun o X => if o = 0 then X else 0

theorem J0_instrument {I : Type} [Fintype I] : IsInstrument (J0 I) := by
  refine ⟨fun o => ?_, fun X => ?_, fun X => ?_⟩
  · by_cases ho : o = 0
    · exact ⟨LinearMap.id, cp_id, fun X => by simp [J0, ho]⟩
    · refine ⟨0, fun r X _ => ?_, fun X => by simp [J0, ho]⟩
      have : idTensorSuperop (R := Fin r) (⇑(0 : Matrix I I ℂ →ₗ[ℂ] Matrix I I ℂ)) X = 0 := rfl
      rw [this]; exact Matrix.PosSemidef.zero
  · apply summable_of_ne_finset_zero (s := {0})
    intro o ho
    simp only [Finset.mem_singleton] at ho
    simp [J0, ho]
  · rw [tsum_eq_single 0 (fun o ho => by simp [J0, ho])]
    simp [J0]

theorem id_instrument {I : Type} [Fintype I] : IsInstrument (fun _ : Unit => (fun X => X : Superop I I)) := by
  refine ⟨fun _ => ⟨LinearMap.id, cp_id, fun X => rfl⟩, fun X => ?_, fun X => ?_⟩
  · exact (hasSum_fintype _).summable
  · rw [tsum_fintype]; simp

theorem id_channel {I : Type} [Fintype I] [DecidableEq I] : IsChannel (fun X => X : Superop I I) := by
  refine ⟨1, fun _ => 1, ?_, fun X => ?_⟩
  · simp [IsKrausFamily]
  · simp [krausApply]

theorem productMap_id {N : ℕ} {d : Fin N → ℕ} :
    productMap (d := d) (fun _ => (fun X => X)) = (fun X => X) := by
  funext X y z
  simp only [productMap, Matrix.single_apply]
  have : ∀ a b : Config d, (∏ k, (if a k = y k ∧ b k = z k then (1:ℂ) else 0))
      = if a = y ∧ b = z then 1 else 0 := by
    intro a b
    rw [Finset.prod_boole]
    congr 1
    apply propext
    simp only [Finset.mem_univ, true_implies, funext_iff]
    exact ⟨fun h => ⟨fun k => (h k).1, fun k => (h k).2⟩, fun h k => ⟨h.1 k, h.2 k⟩⟩
  simp_rw [this]
  simp [ite_and]

theorem productMap_zero {N : ℕ} {d : Fin N → ℕ} (L : (k : Fin N) → Superop (Fin (d k)) (Fin (d k)))
    (k : Fin N) (hk : ∀ X, L k X = 0) : productMap L = fun _ => 0 := by
  funext X y z
  simp only [productMap]
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
  rw [Finset.prod_eq_zero (Finset.mem_univ k) (by rw [hk]; rfl), mul_zero]

theorem J0_oneWay {N : ℕ} (d : Fin N → ℕ) (k : Fin N) : IsOneWay d (J0 (Config d)) := by
  refine ⟨J0_instrument, k, fun o j => if j = k then J0 (Fin (d j)) o else fun X => X,
    ?_, ?_, ?_⟩
  · simpa using (J0_instrument (I := Fin (d k)))
  · intro o j hj
    simp only [hj, if_false]
    exact id_channel
  · intro o
    by_cases ho : o = 0
    · subst ho
      have : (fun j => if j = k then J0 (Fin (d j)) 0 else fun X => X)
          = fun (j : Fin N) => (fun X => X : Superop (Fin (d j)) (Fin (d j))) := by
        funext j X
        by_cases hj : j = k <;> simp [hj, J0]
      show _ = productMap (fun j => if j = k then J0 (Fin (d j)) 0 else fun X => X)
      rw [this, productMap_id]
      funext X; simp [J0]
    · rw [productMap_zero _ k (fun X => by simp [J0, ho])]
      funext X; simp [J0, ho]

theorem J0_extends {N : ℕ} (d : Fin N → ℕ) (k : Fin N) :
    ExtendsHistory d (J0 (Config d)) (J0 (Config d)) := by
  refine ⟨fun _ => J0 (Config d), fun _ => J0_oneWay d k, fun t X => ?_⟩
  by_cases ht : t = 0
  · subst ht; simp [J0, Nat.unpair_zero]
  · have : ¬ ((Nat.unpair t).1 = 0 ∧ (Nat.unpair t).2 = 0) := by
      rintro ⟨h1, h2⟩
      apply ht
      rw [← Nat.pair_unpair t, h1, h2]; rfl
    by_cases h1 : (Nat.unpair t).1 = 0
    · have h2 : (Nat.unpair t).2 ≠ 0 := fun h2 => this ⟨h1, h2⟩
      simp [J0, ht, h2]
    · simp [J0, ht, h1]

theorem traceNorm_zero' {I : Type} [Fintype I] [DecidableEq I] : traceNorm (0 : Matrix I I ℂ) = 0 := by
  simp [traceNorm]

theorem dist_self_zero {I : Type} [Fintype I] [DecidableEq I] :
    instrumentDistance (fun _ : Unit => (fun X => X : Superop I I)) (fun _ : Unit => (fun X => X)) = 0 := by
  unfold instrumentDistance
  have hset : {v : ℝ | ∃ rho : Matrix (I × I) (I × I) ℂ, IsDensityMatrix rho ∧ v = ∑' o : Unit,
      traceNorm (idTensorSuperop (R := I) (fun X : Matrix I I ℂ => X - X) rho)} ⊆ {0} := by
    rintro v ⟨rho, -, rfl⟩
    have : idTensorSuperop (R := I) (fun X : Matrix I I ℂ => X - X) rho = 0 := by
      ext p q; simp [idTensorSuperop]
    rw [this, traceNorm_zero', tsum_zero]; rfl
  rcases Set.subset_singleton_iff_eq.mp hset with h | h
  · rw [h, Real.sSup_empty]
  · rw [h, csSup_singleton]

theorem id_inLOCC {N : ℕ} (d : Fin N → ℕ) (k : Fin N) :
    InLOCC d (fun _ : Unit => (fun X => X : Superop (Config d) (Config d))) := by
  refine ⟨id_instrument, fun _ => J0 (Config d), fun n => ⟨1, one_pos, RawRounds.first _ (J0_oneWay d k)⟩,
    fun n => J0_extends d k, fun _ => fun _ => (fun X => X), fun n => ⟨id_instrument, fun _ => (), fun b X => ?_⟩, ?_⟩
  · simp only [if_true]
    rw [tsum_eq_single 0 (fun o ho => by simp [J0, ho])]
    simp [J0]
  · simp only [dist_self_zero]
    exact tendsto_const_nhds

open QAlgorithms.Papers.Independent.Support50.P04 in
@[simp] theorem pc0 {a b : ℕ} (i : Fin a) (j : Fin b) : pairConfiguration i j 0 = i := rfl
open QAlgorithms.Papers.Independent.Support50.P04 in
@[simp] theorem pc1 {a b : ℕ} (i : Fin a) (j : Fin b) : pairConfiguration i j 1 = j := rfl

@[simp] theorem one_fin1 (u v : Fin 1) : (1 : Matrix (Fin 1) (Fin 1) ℂ) u v = 1 := by
  simp [Matrix.one_apply, Subsingleton.elim u v]

open QAlgorithms.Papers.Independent.Support50.P04 in
theorem marg {B : Type} [Fintype B] [DecidableEq B] (Z : Matrix (Fin 1 × B) (Fin 1 × B) ℂ) :
    receiverConfigurationMarginal
      (conjSuperop (localEmbedding (a := 1) (b := Fintype.card B) (Matrix.of fun _ _ => 1 : Matrix (Fin 1) (Fin 1) ℂ)
        ((1 : Matrix B B ℂ).submatrix (Fintype.equivFin B).symm id)) Z)
      = Z.submatrix (fun j => (0, (Fintype.equivFin B).symm j)) (fun j => (0, (Fintype.equivFin B).symm j)) := by
  ext j k
  simp only [receiverConfigurationMarginal, conjSuperop, localEmbedding, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.submatrix_apply, Fin.sum_univ_one, Fintype.sum_prod_type]
  simp [Matrix.one_apply]

end S176U

open QAlgorithms.Papers.Independent.Support50.P04
open QAlgorithms.Papers.Independent.Information100.P80 (TransmissionCode transmissionFidelity)

theorem solution {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Nonempty A] [Nonempty B]
    (N : Superop A B) (hN : IsChannel N) (C : QAlgorithms.Papers.Independent.Information100.P80.TransmissionCode A B) :
    ∃ D : CppCode A B, D.q = 1 ∧ D.M = C.M ∧
      cppFidelity N D = QAlgorithms.Papers.Independent.Information100.P80.transmissionFidelity N C := by
  set σ := (Fintype.equivFin B).symm
  let W : Matrix (Fin 1) (Fin 1) ℂ := Matrix.of fun _ _ => 1
  let V : Matrix (Fin (Fintype.card B)) B ℂ := (1 : Matrix B B ℂ).submatrix σ id
  let F : Superop (Fin (Fintype.card B)) (Fin C.M) := fun Y => C.decoder (Y.submatrix σ.symm σ.symm)
  have hF : IsChannel F := by
    have := S176U.reindex_channel C.decoder C.decoder_channel σ (Equiv.refl _)
    convert this using 1
    funext Y; ext; simp [F]
  let enc : Superop (Fin C.M) (A × Fin 1) := fun X =>
    (C.encoder (X.submatrix (Equiv.refl (Fin C.M)).symm (Equiv.refl (Fin C.M)).symm)).submatrix
      (Equiv.prodUnique A (Fin 1)) (Equiv.prodUnique A (Fin 1))
  let dec : Superop (Fin 1 × B) (Fin C.M) := fun X =>
    F (receiverConfigurationMarginal ((fun X => X) (conjSuperop (localEmbedding (a := 1) (b := Fintype.card B) W V) X)))
  have hdec : ∀ X, dec X = C.decoder (X.submatrix (Equiv.uniqueProd B (Fin 1)).symm (Equiv.uniqueProd B (Fin 1)).symm) := by
    intro X
    simp only [dec, F, V, W, σ]
    rw [S176U.marg]
    congr 1
    ext b b'
    simp
  have hdecC : IsChannel dec := by
    have := S176U.reindex_channel C.decoder C.decoder_channel (Equiv.uniqueProd B (Fin 1)) (Equiv.refl _)
    convert this using 1
    funext X; rw [hdec]; ext; simp
  have hW : Wᴴ * W = 1 := by
    ext u v; simp [W, Matrix.mul_apply, Matrix.one_apply, Subsingleton.elim u v]
  have hV : Vᴴ * V = 1 := by
    simp only [V, Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one]
    rw [Matrix.submatrix_mul_equiv, Matrix.mul_one, Matrix.submatrix_id_id]
  let D : CppCode A B :=
    { M := C.M, positive := C.positive, q := 1, memory_positive := one_pos,
      encoder := enc,
      encoder_channel := S176U.reindex_channel C.encoder C.encoder_channel _ _,
      decoder := dec,
      decoder_channel := hdecC,
      decoder_locc := ⟨1, Fintype.card B, one_pos, Fintype.card_pos, W, V, hW, hV, fun X => X,
        S176U.id_inLOCC _ 0, F, hF, fun X => rfl⟩ }
  refine ⟨D, rfl, rfl, ?_⟩
  · -- fidelity
    unfold cppFidelity transmissionFidelity
    have heff : cppEffective N D = C.decoder ∘ N ∘ C.encoder := by
      funext X
      show dec (idTensorSuperop (R := Fin 1) N (fun p q => enc X (p.2, p.1) (q.2, q.1))) = _
      rw [hdec]
      congr 1
    have htarget : QAlgorithms.Papers.Independent.Dependency50.P36.target C.M =
        pureDensity (letI : NeZero C.M := ⟨Nat.ne_of_gt C.positive⟩; finiteMaxEntangled (Fin C.M)) := by
      ext p q
      simp only [QAlgorithms.Papers.Independent.Dependency50.P36.target, pureDensity, finiteMaxEntangled,
        Matrix.of_apply]
      by_cases hp : p.1 = p.2 <;> by_cases hq : q.1 = q.2 <;> simp [hp, hq]
      rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]
      simp
    rw [heff, htarget]
