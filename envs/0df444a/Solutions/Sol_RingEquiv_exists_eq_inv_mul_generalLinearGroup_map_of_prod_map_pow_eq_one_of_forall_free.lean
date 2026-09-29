-- Prove2me | solution 1 for RingEquiv.exists_eq_inv_mul_generalLinearGroup_map_of_prod_map_pow_eq_one_of_forall_free
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/eaaa9b46-83d5-5e9c-8720-c9fe26ad2711

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RingEquiv_exists_eq_inv_mul_generalLinearGroup_map_of_prod_map_pow_eq_one_of_forall_free

set_option autoImplicit false

noncomputable section

namespace R4H2D

open Module

section FieldLevel

variable (K L : Type) [Field K] [Field L] [Algebra K L] (σ : L ≃ₐ[K] L) (hσ : 0 < orderOf σ)

abbrev Gσ : Subgroup (L ≃ₐ[K] L) := Subgroup.zpowers σ

abbrev Eσ : Subfield L := FixedPoints.subfield (Gσ K L σ) L

include hσ in
theorem isOfFinOrder_σ : IsOfFinOrder σ := orderOf_pos_iff.mp hσ

@[reducible] noncomputable def fintypeG (hσ : 0 < orderOf σ) : Fintype (Gσ K L σ) :=
  Fintype.ofEquiv _ (finEquivZPowers (isOfFinOrder_σ K L σ hσ))

include hσ in
theorem finite_G : Finite (Gσ K L σ) := by
  haveI := fintypeG K L σ hσ
  infer_instance

include hσ in

theorem sum_aut_eq_sum_pow [Fintype (L ≃ₐ[Eσ K L σ] L)] (z : L) :
    ∑ τ : L ≃ₐ[Eσ K L σ] L, τ z = ∑ k : Fin (orderOf σ), (σ ^ (k : ℕ)) z := by
  haveI := finite_G K L σ hσ
  haveI : Fintype (Gσ K L σ) := fintypeG K L σ hσ
  let e : Gσ K L σ ≃* (L ≃ₐ[Eσ K L σ] L) := FixedPoints.toAlgAutMulEquiv (Gσ K L σ) L
  have h1 : ∑ τ : L ≃ₐ[Eσ K L σ] L, τ z = ∑ g : Gσ K L σ, (e g) z :=
    (Fintype.sum_equiv e.toEquiv (fun g => (e g) z) (fun τ => τ z) (fun _ => rfl)).symm
  have h2 : ∑ g : Gσ K L σ, (e g) z = ∑ g : Gσ K L σ, (g : L ≃ₐ[K] L) z :=
    Finset.sum_congr rfl fun g _ => rfl
  have h3 : ∑ g : Gσ K L σ, (g : L ≃ₐ[K] L) z = ∑ k : Fin (orderOf σ), (σ ^ (k : ℕ)) z := by
    refine (Fintype.sum_equiv (finEquivZPowers (isOfFinOrder_σ K L σ hσ)) _ _ fun k => ?_).symm
    rw [finEquivZPowers_apply]
  rw [h1, h2, h3]

include hσ in

theorem exists_dual_family :
    ∃ (xs ys : Fin (orderOf σ) → L),
      (∀ k : ℕ, k < orderOf σ → ∑ i, xs i * (σ ^ k) (ys i) = if k = 0 then 1 else 0) ∧
      (∀ i j : Fin (orderOf σ), ∑ k ∈ Finset.range (orderOf σ), (σ ^ k) (xs i * ys j) = if i = j then 1 else 0) := by
  classical
  haveI := finite_G K L σ hσ
  haveI : Fintype (Gσ K L σ) := fintypeG K L σ hσ
  set E := Eσ K L σ with hE

  have hrank : finrank E L = orderOf σ := by
    rw [FixedPoints.finrank_eq_card, Fintype.card_congr (finEquivZPowers (isOfFinOrder_σ K L σ hσ)).symm,
      Fintype.card_fin]
  let b : Basis (Fin (orderOf σ)) E L := Module.finBasisOfFinrankEq E L hrank

  have hBnd : (Algebra.traceForm E L).Nondegenerate := traceForm_nondegenerate E L
  let d : Basis (Fin (orderOf σ)) E L := (Algebra.traceForm E L).dualBasis hBnd b
  refine ⟨fun i => d i, fun i => b i, ?_, ?_⟩
  ·
    have hK1 : ∀ z : L, ∑ i, (∑ k : Fin (orderOf σ), (σ ^ (k : ℕ)) (z * b i)) * d i = z := by
      intro z
      have h := d.sum_repr z
      conv_rhs => rw [← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.smul_def, Algebra.traceForm_apply,
        trace_eq_sum_automorphisms, sum_aut_eq_sum_pow K L σ hσ]

    set a : Fin (orderOf σ) → L := fun k => ∑ i, d i * (σ ^ (k : ℕ)) (b i) with ha
    have hsum : ∀ z : L, ∑ k : Fin (orderOf σ), a k * (σ ^ (k : ℕ)) z = z := by
      intro z
      have h := hK1 z
      simp only [map_mul, Finset.sum_mul] at h
      rw [Finset.sum_comm] at h
      have h' : ∑ k : Fin (orderOf σ), a k * (σ ^ (k : ℕ)) z =
          ∑ y : Fin (orderOf σ), ∑ x : Fin (orderOf σ), (σ ^ (y : ℕ)) z * (σ ^ (y : ℕ)) (b x) * d x := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [ha]
        dsimp only
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      rw [h']
      exact h

    have hli : LinearIndependent L (fun k : Fin (orderOf σ) => (((σ ^ (k : ℕ) : L ≃ₐ[K] L) : L →* L) : L → L)) := by
      have h0 := linearIndependent_monoidHom L L
      refine h0.comp (fun k : Fin (orderOf σ) => ((σ ^ (k : ℕ) : L ≃ₐ[K] L) : L →* L)) ?_
      intro k k' hkk'
      have h1 : (σ ^ (k : ℕ)) = σ ^ (k' : ℕ) := by
        apply AlgEquiv.ext
        intro z
        exact congrFun (congrArg (fun f : L →* L => (f : L → L)) hkk') z
      exact Fin.ext (pow_injOn_Iio_orderOf k.2 k'.2 h1)
    rw [Fintype.linearIndependent_iff] at hli
    have hcoef := hli (fun k => a k - if (k : ℕ) = 0 then 1 else 0) (by
      funext z
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, sub_mul, Finset.sum_sub_distrib]
      rw [sub_eq_zero]
      have h2 : ∑ k : Fin (orderOf σ), (if ((k : Fin (orderOf σ)) : ℕ) = 0 then (1 : L) else 0) *
          (((σ ^ (k : ℕ) : L ≃ₐ[K] L) : L →* L) : L → L) z = z := by
        rw [Finset.sum_eq_single (⟨0, hσ⟩ : Fin (orderOf σ))]
        · simp
        · intro k _ hk
          have : (k : ℕ) ≠ 0 := fun h => hk (Fin.ext h)
          simp [this]
        · intro h; exact absurd (Finset.mem_univ _) h
      rw [h2]
      exact hsum z)
    intro k hk
    have hk' := hcoef ⟨k, hk⟩
    rw [sub_eq_zero] at hk'
    exact hk'
  ·
    intro i j
    have h := LinearMap.BilinForm.apply_dualBasis_left hBnd b i j
    rw [Algebra.traceForm_apply] at h
    have h2 := congrArg (algebraMap E L) h
    rw [trace_eq_sum_automorphisms, sum_aut_eq_sum_pow K L σ hσ, Fin.sum_univ_eq_sum_range (fun k => (σ ^ k) _)] at h2
    rw [h2]
    by_cases hij : i = j
    · subst hij; simp
    · have : ¬ j = i := fun h => hij h.symm
      simp [hij, this]

end FieldLevel

section Descent

variable (K L : Type) [Field K] [Field L] [Algebra K L] (σ : L ≃ₐ[K] L) (hσ : 0 < orderOf σ)
  (S : Type) [CommRing S] [Algebra L S] (θ : S ≃+* S)
  (hθ : ∀ l : L, θ (algebraMap L S l) = algebraMap L S (σ l))
  (m : ℕ) (x : GL (Fin m) S)

abbrev Rfix : Subring S := RingHom.eqLocus θ.toRingHom (RingHom.id S)

theorem mem_Rfix {s : S} : s ∈ Rfix S θ ↔ θ s = s := RingHom.mem_eqLocus

theorem θ_coe (r : Rfix S θ) : θ (r : S) = r := (mem_Rfix S θ).mp r.2

theorem θpow_succ_apply (k : ℕ) (s : S) : (θ ^ (k + 1)) s = (θ ^ k) (θ s) := by
  rw [pow_succ]; rfl

theorem σpow_succ_apply (k : ℕ) (l : L) : (σ ^ (k + 1)) l = (σ ^ k) (σ l) := by
  rw [pow_succ]; rfl

theorem θpow_coe (k : ℕ) (r : Rfix S θ) : (θ ^ k) (r : S) = r := by
  induction k with
  | zero => rfl
  | succ k ih => rw [θpow_succ_apply, θ_coe, ih]

include hθ in
theorem θpow_algebraMap (k : ℕ) (l : L) : (θ ^ k) (algebraMap L S l) = algebraMap L S ((σ ^ k) l) := by
  induction k generalizing l with
  | zero => rfl
  | succ k ih => rw [θpow_succ_apply, hθ, ih, σpow_succ_apply]

def trS (s : S) : S := ∑ k ∈ Finset.range (orderOf σ), (θ ^ k) s

omit [Algebra L S] in
theorem θ_trS (hθn : θ ^ orderOf σ = 1) (s : S) : θ (trS K L σ S θ s) = trS K L σ S θ s := by
  unfold trS
  rw [map_sum]
  have h1 : ∀ k, θ ((θ ^ k) s) = (θ ^ (k + 1)) s := fun k => by rw [pow_succ']; rfl
  simp_rw [h1]
  have key := Finset.sum_range_succ' (fun k => (θ ^ k) s) (orderOf σ)
  rw [Finset.sum_range_succ, hθn, pow_zero] at key
  exact add_right_cancel key.symm

omit [Algebra L S] in
theorem trS_mem (hθn : θ ^ orderOf σ = 1) (s : S) : trS K L σ S θ s ∈ Rfix S θ :=
  (mem_Rfix S θ).mpr (θ_trS K L σ S θ hθn s)

omit [Algebra L S] in
theorem trS_mul_coe (s : S) (r : Rfix S θ) : trS K L σ S θ (s * r) = trS K L σ S θ s * r := by
  unfold trS
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, θpow_coe]

include hσ hθ in

theorem exists_dual_family_S :
    ∃ (Xs Ys : Fin (orderOf σ) → S),
      (∀ k : ℕ, k < orderOf σ → ∑ i, Xs i * (θ ^ k) (Ys i) = if k = 0 then 1 else 0) ∧
      (∀ i j : Fin (orderOf σ), trS K L σ S θ (Ys j * Xs i) = if i = j then 1 else 0) := by
  obtain ⟨xs, ys, h4, h5⟩ := exists_dual_family K L σ hσ
  refine ⟨fun i => algebraMap L S (xs i), fun i => algebraMap L S (ys i), ?_, ?_⟩
  · intro k hk
    have h := congrArg (algebraMap L S) (h4 k hk)
    rw [map_sum] at h
    simp only [map_mul] at h
    have h' : ∀ i, algebraMap L S ((σ ^ k) (ys i)) = (θ ^ k) (algebraMap L S (ys i)) := fun i =>
      (θpow_algebraMap K L σ S θ hθ k (ys i)).symm
    simp only [h'] at h
    rw [h]
    split_ifs <;> simp
  · intro i j
    have h := congrArg (algebraMap L S) (h5 i j)
    rw [map_sum] at h
    have h' : ∀ k, algebraMap L S ((σ ^ k) (xs i * ys j)) = (θ ^ k) (algebraMap L S (ys j) * algebraMap L S (xs i)) := by
      intro k
      rw [← θpow_algebraMap K L σ S θ hθ, map_mul, mul_comm]
    simp only [h'] at h
    unfold trS
    rw [h]
    split_ifs <;> simp

def pn (k : ℕ) : GL (Fin m) S :=
  ((List.range k).map fun j => Matrix.GeneralLinearGroup.map ((θ ^ j : S ≃+* S) : S →+* S) x).prod

theorem pn_zero : pn S θ m x 0 = 1 := by simp [pn]

theorem pn_succ (k : ℕ) :
    pn S θ m x (k + 1) = pn S θ m x k * Matrix.GeneralLinearGroup.map ((θ ^ k : S ≃+* S) : S →+* S) x := by
  simp [pn, List.range_succ, List.map_append, List.prod_append]

def Φp (k : ℕ) (v : Fin m → S) : Fin m → S :=
  Matrix.mulVec ((pn S θ m x k : GL (Fin m) S) : Matrix (Fin m) (Fin m) S) (fun j => (θ ^ k) (v j))

def Φ (v : Fin m → S) : Fin m → S :=
  Matrix.mulVec ((x : GL (Fin m) S) : Matrix (Fin m) (Fin m) S) (fun j => θ (v j))

theorem Φp_zero (v : Fin m → S) : Φp S θ m x 0 v = v := by
  unfold Φp
  rw [pn_zero]
  simp

theorem val_map (f : S →+* S) (g : GL (Fin m) S) :
    ((Matrix.GeneralLinearGroup.map (n := Fin m) f g : GL (Fin m) S) : Matrix (Fin m) (Fin m) S) =
      ((g : Matrix (Fin m) (Fin m) S)).map f := rfl

theorem map_θ_map_θpow (k : ℕ) (g : GL (Fin m) S) :
    Matrix.GeneralLinearGroup.map (n := Fin m) (θ : S →+* S)
        (Matrix.GeneralLinearGroup.map ((θ ^ k : S ≃+* S) : S →+* S) g) =
      Matrix.GeneralLinearGroup.map ((θ ^ (k + 1) : S ≃+* S) : S →+* S) g := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.map_apply]
  show θ ((θ ^ k) (g i j)) = (θ ^ (k + 1)) (g i j)
  rw [pow_succ']; rfl

theorem pn_succ' (k : ℕ) :
    pn S θ m x (k + 1) = x * Matrix.GeneralLinearGroup.map (n := Fin m) (θ : S →+* S) (pn S θ m x k) := by
  induction k with
  | zero =>
      rw [pn_succ, pn_zero, one_mul, map_one, mul_one, pow_zero]
      refine Matrix.GeneralLinearGroup.ext fun i j => ?_
      rw [Matrix.GeneralLinearGroup.map_apply]
      rfl
  | succ k ih =>
      rw [pn_succ, ih, mul_assoc, ← map_θ_map_θpow, ← map_mul, ← pn_succ, ← ih]

theorem Φ_Φp (k : ℕ) (v : Fin m → S) : Φ S θ m x (Φp S θ m x k v) = Φp S θ m x (k + 1) v := by
  unfold Φ Φp
  rw [pn_succ', Units.val_mul, ← Matrix.mulVec_mulVec, val_map]
  congr 1
  funext i
  have h := RingHom.map_mulVec (θ : S →+* S) ((pn S θ m x k : GL (Fin m) S) : Matrix (Fin m) (Fin m) S)
    (fun j => (θ ^ k) (v j)) i
  simp only [RingHom.coe_coe] at h
  have hfg : ((⇑θ) ∘ fun j => (θ ^ k) (v j)) = fun j => (θ ^ (k + 1)) (v j) := by
    funext j
    show θ ((θ ^ k) (v j)) = (θ ^ (k + 1)) (v j)
    rw [pow_succ']; rfl
  rw [hfg] at h
  exact h

omit [Algebra L S] in

theorem Φp_orderOf (hθn : θ ^ orderOf σ = 1)
    (hx : ((List.range (orderOf σ)).map
      fun k => Matrix.GeneralLinearGroup.map ((θ ^ k : S ≃+* S) : S →+* S) x).prod = 1)
    (v : Fin m → S) : Φp S θ m x (orderOf σ) v = v := by
  unfold Φp
  have h : pn S θ m x (orderOf σ) = 1 := hx
  rw [h, hθn]
  simp

theorem Φp_smul (k : ℕ) (s : S) (v : Fin m → S) : Φp S θ m x k (s • v) = (θ ^ k) s • Φp S θ m x k v := by
  unfold Φp
  rw [← Matrix.mulVec_smul]
  congr 1
  funext j
  simp [Pi.smul_apply, smul_eq_mul, map_mul]

theorem Φp_add (k : ℕ) (v w : Fin m → S) : Φp S θ m x k (v + w) = Φp S θ m x k v + Φp S θ m x k w := by
  unfold Φp
  rw [← Matrix.mulVec_add]
  congr 1
  funext j
  simp [map_add]

theorem Φ_add (v w : Fin m → S) : Φ S θ m x (v + w) = Φ S θ m x v + Φ S θ m x w := by
  unfold Φ
  rw [← Matrix.mulVec_add]
  congr 1
  funext j
  simp [map_add]

theorem Φ_smul (s : S) (v : Fin m → S) : Φ S θ m x (s • v) = θ s • Φ S θ m x v := by
  unfold Φ
  rw [← Matrix.mulVec_smul]
  congr 1
  funext j
  simp [Pi.smul_apply, smul_eq_mul, map_mul]

theorem Φp_of_fixed (v : Fin m → S) (hv : Φ S θ m x v = v) (k : ℕ) : Φp S θ m x k v = v := by
  induction k with
  | zero => exact Φp_zero S θ m x v
  | succ k ih => rw [← Φ_Φp, ih, hv]

def tr (v : Fin m → S) : Fin m → S := ∑ k ∈ Finset.range (orderOf σ), Φp S θ m x k v

theorem Φ_sum (s : Finset ℕ) (f : ℕ → Fin m → S) : Φ S θ m x (∑ k ∈ s, f k) = ∑ k ∈ s, Φ S θ m x (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty]
      unfold Φ
      have : (fun j => θ ((0 : Fin m → S) j)) = 0 := by funext j; simp
      rw [this, Matrix.mulVec_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Φ_add, ih]

omit [Algebra L S] in
theorem Φ_tr (hθn : θ ^ orderOf σ = 1)
    (hx : ((List.range (orderOf σ)).map
      fun k => Matrix.GeneralLinearGroup.map ((θ ^ k : S ≃+* S) : S →+* S) x).prod = 1)
    (v : Fin m → S) : Φ S θ m x (tr K L σ S θ m x v) = tr K L σ S θ m x v := by
  unfold tr
  rw [Φ_sum]
  simp_rw [Φ_Φp]
  have key := Finset.sum_range_succ' (fun k => Φp S θ m x k v) (orderOf σ)
  rw [Finset.sum_range_succ, Φp_orderOf K L σ S θ m x hθn hx, Φp_zero] at key
  exact add_right_cancel key.symm

omit [Algebra L S] in
theorem tr_add (v w : Fin m → S) : tr K L σ S θ m x (v + w) = tr K L σ S θ m x v + tr K L σ S θ m x w := by
  unfold tr
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => Φp_add S θ m x k v w

omit [Algebra L S] in
theorem tr_smul_fixed (v : Fin m → S) (hv : Φ S θ m x v = v) (s : S) :
    tr K L σ S θ m x (s • v) = trS K L σ S θ s • v := by
  unfold tr trS
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Φp_smul, Φp_of_fixed S θ m x v hv]

omit [Algebra L S] in
theorem tr_sum {ι : Type} (s : Finset ι) (f : ι → Fin m → S) :
    tr K L σ S θ m x (∑ i ∈ s, f i) = ∑ i ∈ s, tr K L σ S θ m x (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty]
      unfold tr
      refine Finset.sum_eq_zero fun k _ => ?_
      unfold Φp
      have : (fun j => (θ ^ k) ((0 : Fin m → S) j)) = 0 := by funext j; simp
      rw [this, Matrix.mulVec_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, tr_add, ih]

theorem subring_smul_apply (r : Rfix S θ) (v : Fin m → S) (j : Fin m) : (r • v) j = (r : S) * v j := rfl

theorem subring_smul_eq (r : Rfix S θ) (v : Fin m → S) : (r • v) = ((r : S) • v) := rfl

def Minv : Submodule (Rfix S θ) (Fin m → S) where
  carrier := {v | Φ S θ m x v = v}
  add_mem' {v w} hv hw := by
    show Φ S θ m x (v + w) = v + w
    rw [Φ_add, hv, hw]
  zero_mem' := by
    show Φ S θ m x 0 = 0
    unfold Φ
    have : (fun j => θ ((0 : Fin m → S) j)) = 0 := by funext j; simp
    rw [this, Matrix.mulVec_zero]
  smul_mem' r v hv := by
    show Φ S θ m x (r • v) = r • v
    rw [subring_smul_eq, Φ_smul, θ_coe, hv]

theorem mem_Minv {v : Fin m → S} : v ∈ Minv S θ m x ↔ Φ S θ m x v = v := Iff.rfl

variable (hθn : θ ^ orderOf σ = 1)
  (hx : ((List.range (orderOf σ)).map
      fun k => Matrix.GeneralLinearGroup.map ((θ ^ k : S ≃+* S) : S →+* S) x).prod = 1)

omit [Algebra L S] in
include hθn hx in
theorem tr_mem (v : Fin m → S) : tr K L σ S θ m x v ∈ Minv S θ m x :=
  (mem_Minv S θ m x).mpr (Φ_tr K L σ S θ m x hθn hx v)

section WithDual

variable (Xs Ys : Fin (orderOf σ) → S)
  (h4 : ∀ k : ℕ, k < orderOf σ → ∑ i, Xs i * (θ ^ k) (Ys i) = if k = 0 then 1 else 0)
  (h5 : ∀ i j : Fin (orderOf σ), trS K L σ S θ (Ys j * Xs i) = if i = j then 1 else 0)

omit [Algebra L S] in
include h4 hσ in

theorem sum_Xs_tr (v : Fin m → S) : ∑ i, Xs i • tr K L σ S θ m x (Ys i • v) = v := by
  unfold tr
  have h1 : ∀ i, Xs i • ∑ k ∈ Finset.range (orderOf σ), Φp S θ m x k (Ys i • v) =
      ∑ k ∈ Finset.range (orderOf σ), (Xs i * (θ ^ k) (Ys i)) • Φp S θ m x k v := by
    intro i
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Φp_smul, smul_smul]
  simp_rw [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ k ∈ Finset.range (orderOf σ),
      ∑ i, (Xs i * (θ ^ k) (Ys i)) • Φp S θ m x k v = (if k = 0 then (1 : S) else 0) • Φp S θ m x k v := by
    intro k hk
    rw [← Finset.sum_smul, h4 k (Finset.mem_range.mp hk)]
  rw [Finset.sum_congr rfl h2]
  simp only [ite_smul, one_smul, zero_smul]
  rw [Finset.sum_ite_eq' (Finset.range (orderOf σ)) 0 (fun k => Φp S θ m x k v)]
  rw [if_pos (Finset.mem_range.mpr hσ), Φp_zero]

omit [Algebra L S] in
include h4 hσ in

theorem sum_Xs_trS (s : S) : ∑ i, Xs i * trS K L σ S θ (Ys i * s) = s := by
  unfold trS
  have h1 : ∀ i, Xs i * ∑ k ∈ Finset.range (orderOf σ), (θ ^ k) (Ys i * s) =
      ∑ k ∈ Finset.range (orderOf σ), (Xs i * (θ ^ k) (Ys i)) * (θ ^ k) s := by
    intro i
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, mul_assoc]
  simp_rw [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ k ∈ Finset.range (orderOf σ),
      ∑ i, (Xs i * (θ ^ k) (Ys i)) * (θ ^ k) s = (if k = 0 then (1 : S) else 0) * (θ ^ k) s := by
    intro k hk
    rw [← Finset.sum_mul, h4 k (Finset.mem_range.mp hk)]
  rw [Finset.sum_congr rfl h2]
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' (Finset.range (orderOf σ)) 0 (fun k => (θ ^ k) s)]
  rw [if_pos (Finset.mem_range.mpr hσ), pow_zero]
  rfl

omit [Algebra L S] in
include h5 in

theorem tr_Ys_sum (w : Fin (orderOf σ) → Fin m → S) (hw : ∀ i, Φ S θ m x (w i) = w i) (j : Fin (orderOf σ)) :
    tr K L σ S θ m x (Ys j • ∑ i, Xs i • w i) = w j := by
  rw [Finset.smul_sum, tr_sum]
  have h1 : ∀ i, tr K L σ S θ m x (Ys j • Xs i • w i) = (trS K L σ S θ (Ys j * Xs i)) • w i := by
    intro i
    rw [smul_smul, tr_smul_fixed K L σ S θ m x (w i) (hw i)]
  simp_rw [h1, h5]
  simp only [ite_smul, one_smul, zero_smul]
  rw [Finset.sum_ite_eq' Finset.univ j (fun i => w i), if_pos (Finset.mem_univ j)]

omit [Algebra L S] in
include h5 in
theorem trS_Ys_sum (r : Fin (orderOf σ) → Rfix S θ) (j : Fin (orderOf σ)) :
    trS K L σ S θ (Ys j * ∑ i, Xs i * (r i : S)) = r j := by
  rw [Finset.mul_sum]
  unfold trS
  simp_rw [map_sum]
  rw [Finset.sum_comm]
  have h1 : ∀ i, ∑ k ∈ Finset.range (orderOf σ), (θ ^ k) (Ys j * (Xs i * (r i : S))) =
      trS K L σ S θ (Ys j * Xs i) * (r i : S) := by
    intro i
    unfold trS
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← mul_assoc, map_mul, θpow_coe]
  simp_rw [h1, h5]
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ j (fun i => (r i : S)), if_pos (Finset.mem_univ j)]

include hσ hθn hx h4 h5 in

def descentEquiv : (Fin (orderOf σ) → Minv S θ m x) ≃ₗ[Rfix S θ] (Fin m → S) where
  toFun w := ∑ i, Xs i • (w i : Fin m → S)
  invFun v := fun i => ⟨tr K L σ S θ m x (Ys i • v), tr_mem K L σ S θ m x hθn hx _⟩
  map_add' w w' := by
    show ∑ i, Xs i • ((w + w') i : Fin m → S) = ∑ i, Xs i • (w i : Fin m → S) + ∑ i, Xs i • (w' i : Fin m → S)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.add_apply, Submodule.coe_add, smul_add]
  map_smul' r w := by
    show ∑ i, Xs i • ((r • w) i : Fin m → S) = r • ∑ i, Xs i • (w i : Fin m → S)
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, Submodule.coe_smul, subring_smul_eq, subring_smul_eq, smul_comm]
  left_inv w := by
    funext j
    apply Subtype.ext
    show tr K L σ S θ m x (Ys j • ∑ i, Xs i • (w i : Fin m → S)) = (w j : Fin m → S)
    exact tr_Ys_sum K L σ S θ m x Xs Ys h5 (fun i => (w i : Fin m → S)) (fun i => (mem_Minv S θ m x).mp (w i).2) j
  right_inv v := sum_Xs_tr K L σ hσ S θ m x Xs Ys h4 v

include hσ hθn h4 h5 in

def baseEquiv : (Fin (orderOf σ) → Rfix S θ) ≃ₗ[Rfix S θ] S where
  toFun r := ∑ i, Xs i * (r i : S)
  invFun s := fun i => ⟨trS K L σ S θ (Ys i * s), trS_mem K L σ S θ hθn _⟩
  map_add' r r' := by
    show ∑ i, Xs i * (((r + r') i : Rfix S θ) : S) = ∑ i, Xs i * (r i : S) + ∑ i, Xs i * (r' i : S)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.add_apply, Subring.coe_add, mul_add]
  map_smul' c r := by
    show ∑ i, Xs i * (((c • r) i : Rfix S θ) : S) = c • ∑ i, Xs i * (r i : S)
    rw [Subring.smul_def, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, Subring.coe_mul]
    ring
  left_inv r := by
    funext j
    apply Subtype.ext
    exact trS_Ys_sum K L σ S θ Xs Ys h5 r j
  right_inv s := sum_Xs_trS K L σ hσ S θ Xs Ys h4 s

include hσ hθn hx h4 h5 in

def hfreeEquiv : (Fin (orderOf σ) → Minv S θ m x) ≃ₗ[Rfix S θ] (Fin (m * orderOf σ) → Rfix S θ) :=
  (descentEquiv K L σ hσ S θ m x hθn hx Xs Ys h4 h5).trans
    ((LinearEquiv.piCongrRight fun _ : Fin m => (baseEquiv K L σ hσ S θ hθn Xs Ys h4 h5).symm).trans
      ((LinearEquiv.curry (Rfix S θ) (Rfix S θ) (Fin m) (Fin (orderOf σ))).symm.trans
        (LinearEquiv.funCongrLeft (Rfix S θ) (Rfix S θ) finProdFinEquiv.symm)))

theorem exists_inverse_of_span (u : Fin m → Fin m → S)
    (hspan : ∀ v : Fin m → S, ∃ c : Fin m → S, ∑ j, c j • u j = v) :
    ∃ C : Matrix (Fin m) (Fin m) S,
      (Matrix.of fun i j => u j i) * C = 1 ∧ C * (Matrix.of fun i j => u j i) = 1 := by
  classical
  choose c hc using hspan
  set U : Matrix (Fin m) (Fin m) S := Matrix.of fun i j => u j i with hU
  set C : Matrix (Fin m) (Fin m) S := Matrix.of fun j k => c (Pi.single k 1) j with hC
  have hUC : U * C = 1 := by
    ext l k
    rw [Matrix.mul_apply, Matrix.one_apply]
    have h := congrFun (hc (Pi.single k 1)) l
    rw [Finset.sum_apply] at h
    simp only [Pi.smul_apply, smul_eq_mul] at h
    rw [Pi.single_apply] at h
    rw [hU, hC]
    simp only [Matrix.of_apply]
    rw [← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  exact ⟨C, hUC, mul_eq_one_comm.mp hUC⟩

omit [Algebra L S] in
include hσ hθn hx h4 h5 in

theorem exists_coboundary [Nontrivial S]
    (hfree : ∀ (P : Type) [AddCommGroup P] [Module (Rfix S θ) P],
      ((Fin (orderOf σ) → P) ≃ₗ[Rfix S θ] (Fin (m * orderOf σ) → Rfix S θ)) → Module.Free (Rfix S θ) P) :
    ∃ y : GL (Fin m) S, x = y⁻¹ * Matrix.GeneralLinearGroup.map (θ : S →+* S) y := by
  classical
  set M := Minv S θ m x with hM

  let eM := hfreeEquiv K L σ hσ S θ m x hθn hx Xs Ys h4 h5
  haveI hMfree : Module.Free (Rfix S θ) M := hfree M eM

  haveI : Module.Finite (Rfix S θ) (Fin (orderOf σ) → M) := Module.Finite.equiv eM.symm
  haveI hMfin : Module.Finite (Rfix S θ) M :=
    Module.Finite.of_surjective (LinearMap.proj (⟨0, hσ⟩ : Fin (orderOf σ)) : (Fin (orderOf σ) → M) →ₗ[Rfix S θ] M)
      (fun v => ⟨fun _ => v, rfl⟩)

  have hrank : Module.finrank (Rfix S θ) M = m := by
    have h1 := eM.finrank_eq
    rw [Module.finrank_pi_fintype, Module.finrank_fin_fun, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul] at h1

    have h2 : orderOf σ * Module.finrank (Rfix S θ) M = orderOf σ * m := by rw [h1, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left hσ h2
  let bM : Module.Basis (Fin m) (Rfix S θ) M := Module.finBasisOfFinrankEq (Rfix S θ) M hrank

  set u : Fin m → Fin m → S := fun j => ((bM j : M) : Fin m → S) with hu
  have hufix : ∀ j, Φ S θ m x (u j) = u j := fun j => (mem_Minv S θ m x).mp (bM j).2

  have hspan : ∀ v : Fin m → S, ∃ c : Fin m → S, ∑ j, c j • u j = v := by
    intro v
    let w := (descentEquiv K L σ hσ S θ m x hθn hx Xs Ys h4 h5).symm v
    have hv : ∑ i, Xs i • (w i : Fin m → S) = v :=
      (descentEquiv K L σ hσ S θ m x hθn hx Xs Ys h4 h5).apply_symm_apply v
    refine ⟨fun j => ∑ i, Xs i * ((bM.repr (w i) j : Rfix S θ) : S), ?_⟩
    rw [← hv]
    have hw : ∀ i, ((w i : M) : Fin m → S) = ∑ j, ((bM.repr (w i) j : Rfix S θ) : S) • u j := by
      intro i
      have h := bM.sum_repr (w i)
      have h' := congrArg (fun z : M => (z : Fin m → S)) h
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h'
      rw [← h']
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [subring_smul_eq]
    simp_rw [hw, Finset.smul_sum, smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm]
  obtain ⟨C, hUC, hCU⟩ := exists_inverse_of_span S m u hspan
  set U : Matrix (Fin m) (Fin m) S := Matrix.of fun i j => u j i with hU

  have hxU : ((x : GL (Fin m) S) : Matrix (Fin m) (Fin m) S) * U.map θ = U := by
    ext i j
    have h := congrFun (hufix j) i
    unfold Φ at h
    rw [Matrix.mul_apply]
    rw [Matrix.mulVec, dotProduct] at h
    rw [hU]
    simp only [Matrix.map_apply, Matrix.of_apply]
    rw [← h]

  let Uu : GL (Fin m) S := ⟨U, C, hUC, hCU⟩
  have hmap : ((Matrix.GeneralLinearGroup.map (n := Fin m) (θ : S →+* S) Uu : GL (Fin m) S) :
      Matrix (Fin m) (Fin m) S) = U.map θ := rfl
  have hxUu : x * Matrix.GeneralLinearGroup.map (n := Fin m) (θ : S →+* S) Uu = Uu := by
    apply Units.ext
    rw [Units.val_mul, hmap]
    exact hxU
  refine ⟨Uu⁻¹, ?_⟩
  rw [inv_inv, map_inv]
  exact eq_mul_inv_of_mul_eq hxUu

end WithDual

include hσ hθ in
theorem main (hθn : θ ^ orderOf σ = 1)
    (hfree : ∀ (P : Type) [AddCommGroup P] [Module (RingHom.eqLocus θ.toRingHom (RingHom.id S)) P],
      ((Fin (orderOf σ) → P) ≃ₗ[RingHom.eqLocus θ.toRingHom (RingHom.id S)]
          (Fin (m * orderOf σ) → RingHom.eqLocus θ.toRingHom (RingHom.id S))) →
        Module.Free (RingHom.eqLocus θ.toRingHom (RingHom.id S)) P)
    (hx : ((List.range (orderOf σ)).map
      fun k => Matrix.GeneralLinearGroup.map ((θ ^ k : S ≃+* S) : S →+* S) x).prod = 1) :
    ∃ y : GL (Fin m) S, x = y⁻¹ * Matrix.GeneralLinearGroup.map (θ : S →+* S) y := by
  rcases subsingleton_or_nontrivial S with hS | hS
  · refine ⟨1, Units.ext (Subsingleton.elim _ _)⟩
  · obtain ⟨Xs, Ys, h4, h5⟩ := exists_dual_family_S K L σ hσ S θ hθ
    exact exists_coboundary K L σ hσ S θ m x hθn hx Xs Ys h4 h5 hfree

end Descent

end R4H2D

end

theorem solution
    (K L : Type) [Field K] [Field L] [Algebra K L] (σ : L ≃ₐ[K] L) (hσ : 0 < orderOf σ)
    (S : Type) [CommRing S] [Algebra L S] (θ : S ≃+* S)
    (hθ : ∀ l : L, θ (algebraMap L S l) = algebraMap L S (σ l))
    (hθn : θ ^ orderOf σ = 1)
    (m : ℕ)
    (hfree : ∀ (P : Type) [AddCommGroup P] [Module (RingHom.eqLocus θ.toRingHom (RingHom.id S)) P],
      ((Fin (orderOf σ) → P) ≃ₗ[RingHom.eqLocus θ.toRingHom (RingHom.id S)]
          (Fin (m * orderOf σ) → RingHom.eqLocus θ.toRingHom (RingHom.id S))) →
        Module.Free (RingHom.eqLocus θ.toRingHom (RingHom.id S)) P)
    (x : GL (Fin m) S)
    (hx : ((List.range (orderOf σ)).map
      fun k => Matrix.GeneralLinearGroup.map ((θ ^ k : S ≃+* S) : S →+* S) x).prod = 1) :
    ∃ y : GL (Fin m) S, x = y⁻¹ * Matrix.GeneralLinearGroup.map (θ : S →+* S) y :=
  R4H2D.main K L σ hσ S θ hθ m x hθn hfree hx

end S_RingEquiv_exists_eq_inv_mul_generalLinearGroup_map_of_prod_map_pow_eq_one_of_forall_free
end P2MW
export P2MW.S_RingEquiv_exists_eq_inv_mul_generalLinearGroup_map_of_prod_map_pow_eq_one_of_forall_free (solution)
