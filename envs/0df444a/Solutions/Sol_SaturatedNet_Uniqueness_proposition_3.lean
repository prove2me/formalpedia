-- Prove2me | solution 1 for SaturatedNet.Uniqueness.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T10:17:03.59272+00:00
-- url     : https://prove2.me/submissions/dc10028e-ab39-487e-a6c5-0327af8b778c

import Mathlib
import Definitions.Def_SaturatedNet_Uniqueness_Model
import Theorems.Thm_SaturatedNet_Uniqueness_lemma_1
import Theorems.Thm_SaturatedNet_Uniqueness_proposition_2_i_ii

-- All local graph, spectral, transport, and subcritical helper proofs are included below.
-- Subcritical.lean was contributed in this same task scope and is inlined in full.

-- Graph

open Matrix
namespace SaturatedNet.Uniqueness.NonexpansiveProof

lemma class_reaches {n : Type*} (P : Matrix n n ℝ) {V : Finset n}
    (hV : IsClass P V) {i j : n} (hi : i ∈ V) (hj : j ∈ V) : Reaches P i j := by
  obtain ⟨a,ha,h⟩ := hV
  exact ((h i).mp hi).2.trans ((h j).mp hj).1

lemma class_between {n : Type*} (P : Matrix n n ℝ) {V : Finset n}
    (hV : IsClass P V) {i j k : n} (hi : i ∈ V) (hk : k ∈ V)
    (hij : Reaches P i j) (hjk : Reaches P j k) : j ∈ V := by
  obtain ⟨a,ha,h⟩ := hV
  apply (h j).mpr
  exact ⟨((h i).mp hi).1.trans hij, hjk.trans ((h k).mp hk).2⟩

lemma reaches_block {n : Type*} (P : Matrix n n ℝ) {V : Finset n}
    (hV : IsClass P V) {i j : n} (hij : Reaches P i j)
    (hi : i ∈ V) (hj : j ∈ V) : Reaches (block P V) ⟨i,hi⟩ ⟨j,hj⟩ := by
  revert hi hj
  induction hij with
  | refl => intro hi hj; exact Relation.ReflTransGen.refl
  | @tail j k hij hjk ih =>
    intro hi hk
    have hj := class_between P hV hi hk hij (Relation.ReflTransGen.single hjk)
    exact Relation.ReflTransGen.tail (ih hi hj) hjk

lemma block_reaches {n : Type*} (P : Matrix n n ℝ) (V : Finset n)
    {i j : V} (hij : Reaches (block P V) i j) : Reaches P i j := by
  induction hij with
  | refl => exact Relation.ReflTransGen.refl
  | @tail j k hij hjk ih => exact Relation.ReflTransGen.tail ih hjk

lemma eigenvector_pos_on_class {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j) (V : Finset n) (hV : IsClass P V)
    (v : V → ℝ) (hv : 0 ≤ v) (hne : v ≠ 0) (lam : ℝ)
    (he : block P V *ᵥ v = lam • v) : ∀ i, 0 < v i := by
  classical
  have zero_edge (i j : V) (hi : v i=0) (hij : block P V i j≠0) : v j=0 := by
    have hsum : ∑ k : V, block P V i k * v k = 0 := by
      have hh : (block P V *ᵥ v) i = 0 := by simpa [hi] using congrFun he i
      exact hh
    have hjzero : block P V i j * v j=0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun (k : V) _ => mul_nonneg (hP i k) (hv k))).mp hsum j (Finset.mem_univ j)
    exact (mul_eq_zero.mp hjzero).resolve_left hij
  have zero_reaches (a b : V) (h : Reaches (block P V) a b) (ha : v a=0) : v b=0 := by
    induction h with
    | refl => exact ha
    | @tail j k hjk hejk ih => exact zero_edge j k ih hejk
  intro i
  by_contra hn
  have hi : v i=0 := le_antisymm (le_of_not_gt hn) (hv i)
  apply hne
  funext j
  have hij := reaches_block P hV (class_reaches P hV i.property j.property) i.property j.property
  exact zero_reaches i j hij hi

lemma exists_source_class {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (P : Matrix n n ℝ) :
    ∃ V : Finset n, IsClass P V ∧ ∀ i ∉ V, ∀ j ∈ V, P i j=0 := by
  classical
  let pred (i : n) : Finset n := Finset.univ.filter (fun j => Reaches P j i)
  obtain ⟨a,_,ha⟩ := Finset.exists_min_image Finset.univ (fun i => (pred i).card) Finset.univ_nonempty
  have hpred (i j : n) : j ∈ pred i ↔ Reaches P j i := by simp [pred]
  have hback (i : n) (hi : Reaches P i a) : Reaches P a i := by
    have hsub : pred i ⊆ pred a := by
      intro j hj
      exact (hpred a j).mpr (((hpred i j).mp hj).trans hi)
    have heq : pred i=pred a := Finset.eq_of_subset_of_card_le hsub (ha i (Finset.mem_univ i))
    have haa : a ∈ pred a := (hpred a a).mpr Relation.ReflTransGen.refl
    exact (hpred i a).mp (heq ▸ haa)
  refine ⟨pred a,?_,?_⟩
  · refine ⟨a,(hpred a a).mpr Relation.ReflTransGen.refl,?_⟩
    intro i
    rw [hpred]
    exact ⟨fun hi => ⟨hback i hi,hi⟩,fun hi => hi.2⟩
  · intro i hi j hj
    by_contra hij
    exact hi ((hpred a i).mpr ((Relation.ReflTransGen.single hij).trans ((hpred a j).mp hj)))

end SaturatedNet.Uniqueness.NonexpansiveProof

-- SpectrumBound

open Matrix
namespace SaturatedNet.Uniqueness.NonexpansiveProof

lemma spectral_radius_le_one_of_supersolution {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j)
    (v : n → ℝ) (hv : ∀ i, 0 < v i) (hPv : P*ᵥv≤v) : specRad P≤1 := by
  classical
  unfold specRad spectralRadius
  apply iSup_le
  intro μ
  apply iSup_le
  intro hμ
  let A := P.map (algebraMap ℝ ℂ)
  have heigen : Module.End.HasEigenvalue A.toLin' μ := Module.End.HasEigenvalue.of_mem_spectrum (by
    rwa [Matrix.spectrum_toLin'])
  obtain ⟨z,hz⟩ := heigen.exists_hasEigenvector
  have heq : A*ᵥz=μ•z := hz.apply_eq_smul
  obtain ⟨j,hj⟩ := Function.ne_iff.mp hz.2
  have hzj : 0 < ‖z j‖ := norm_pos_iff.mpr hj
  obtain ⟨i,_,hmax⟩ := Finset.exists_max_image Finset.univ (fun k => ‖z k‖/v k)
    ⟨j,Finset.mem_univ j⟩
  let r := ‖z i‖/v i
  have hr : 0 < r := (div_pos hzj (hv j)).trans_le (hmax j (Finset.mem_univ j))
  have hb (k : n) : ‖z k‖ ≤ r*v k := (div_le_iff₀ (hv k)).mp (hmax k (Finset.mem_univ k))
  have he : ‖z i‖=r*v i := (div_mul_cancel₀ _ (hv i).ne').symm
  have hzi : 0 < ‖z i‖ := he ▸ mul_pos hr (hv i)
  have hi : ∑ k, (P i k : ℂ)*z k=μ*z i := congrFun heq i
  have hbound : ‖μ‖*‖z i‖ ≤ ‖z i‖ := calc
    ‖μ‖*‖z i‖ = ‖μ*z i‖ := (norm_mul _ _).symm
    _ = ‖∑ k, (P i k : ℂ)*z k‖ := congrArg norm hi.symm
    _ ≤ ∑ k, ‖(P i k : ℂ)*z k‖ := norm_sum_le _ _
    _ = ∑ k, P i k*‖z k‖ := by
      simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hP i _)]
    _ ≤ ∑ k, P i k*(r*v k) := Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hb k) (hP i k)
    _ = r*(P*ᵥv) i := by
      simp only [Matrix.mulVec,dotProduct,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ ≤ r*v i := mul_le_mul_of_nonneg_left (hPv i) hr.le
    _ = ‖z i‖ := he.symm
  have hμle : ‖μ‖≤1 := (mul_le_mul_iff_left₀ hzi).mp (by simpa only [one_mul] using hbound)
  exact_mod_cast hμle

end SaturatedNet.Uniqueness.NonexpansiveProof

-- Forward

open Matrix
namespace SaturatedNet.Uniqueness.NonexpansiveProof

lemma row_split {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (V : Finset n) (v : n → ℝ) (i : n) :
    (P*ᵥv) i = (∑ j : V, P i j*v j) + ∑ j : (Vᶜ : Finset n), P i j*v j := by
  have h1 := Finset.sum_coe_sort V (fun j : n => P i j*v j)
  have h2 := Finset.sum_coe_sort (Vᶜ : Finset n) (fun j : n => P i j*v j)
  rw [h1,h2]
  exact (Finset.sum_add_sum_compl V (fun j => P i j*v j)).symm

lemma block_subinvariant {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j) (V : Finset n)
    (v : n → ℝ) (hv : 0 ≤ v) (hPv : P*ᵥv≤v) :
    block P V *ᵥ (fun i : V => v i) ≤ (fun i : V => v i) := by
  intro i
  have hnonneg : 0 ≤ ∑ j : (Vᶜ : Finset n), P i j*v j :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hP i j) (hv j)
  have hi := hPv i
  rw [row_split P V v i] at hi
  change (∑ j : V, P i j*v j) ≤ v i
  linarith

lemma critical_class_final {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j)
    (v : n → ℝ) (hv : ∀ i, 0 < v i) (hPv : P*ᵥv≤v)
    (V : Finset n) (hV : IsClass P V) (hr : specRad (block P V)=1) : IsFinal P V := by
  classical
  intro i hi j hj
  by_contra hpij
  have hout : 0 < ∑ k : (Vᶜ : Finset n), P i k*v k := by
    let j' : (Vᶜ : Finset n) := ⟨j,Finset.mem_compl.mpr hj⟩
    apply (mul_pos (lt_of_le_of_ne (hP i j) (Ne.symm hpij)) (hv j)).trans_le
    exact Finset.single_le_sum (fun (k : (Vᶜ : Finset n)) _ => mul_nonneg (hP i k) (hv k).le) (Finset.mem_univ j')
  have hstrict : (block P V *ᵥ (fun k : V => v k)) ⟨i,hi⟩ < v i := by
    have hi' := hPv i
    rw [row_split P V v i] at hi'
    change (∑ k : V, P i k*v k) < v i
    linarith
  have hne : (fun k : V => v k) ≠ 0 := by
    intro he
    have he' : v i=0 := congrFun he ⟨i,hi⟩
    exact (hv i).ne' he'
  have hs := SaturatedNet.Uniqueness.lemma_1 (block P V) (fun k l => hP k l)
    (fun k : V => v k) (fun k => (hv k).le) hne
    (block_subinvariant P hP V v (fun k => (hv k).le) hPv)
    (fun k => ⟨⟨i,hi⟩,reaches_block P hV (class_reaches P hV k.property hi) k.property hi,hstrict⟩)
  rw [hr] at hs
  exact lt_irrefl _ hs

lemma forward {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j)
    (v : n → ℝ) (hv : ∀ i, 0 < v i) (hPv : P*ᵥv≤v) :
    specRad P < 1 ∨ (specRad P=1 ∧ ∀ V, IsClass P V → IsBasic P V → IsFinal P V) := by
  rcases lt_or_eq_of_le (spectral_radius_le_one_of_supersolution P hP v hv hPv) with hr|hr
  · exact Or.inl hr
  · refine Or.inr ⟨hr,?_⟩
    intro V hV hbasic
    exact critical_class_final P hP v hv hPv V hV (hbasic.trans hr)

end SaturatedNet.Uniqueness.NonexpansiveProof

-- Transport

open Matrix
namespace SaturatedNet.Uniqueness.NonexpansiveProof

lemma reaches_mem_of_final {n : Type*} (P : Matrix n n ℝ) (W : Finset n)
    (hW : IsFinal P W) {i j : n} (hi : i ∈ W) (hij : Reaches P i j) : j ∈ W := by
  induction hij with
  | refl => exact hi
  | @tail j k hij hjk ih =>
    by_contra hk
    exact hjk (hW j ih k hk)

lemma reaches_restrict_final {n : Type*} (P : Matrix n n ℝ) (W : Finset n)
    (hW : IsFinal P W) {i j : n} (hij : Reaches P i j)
    (hi : i ∈ W) (hj : j ∈ W) : Reaches (block P W) ⟨i,hi⟩ ⟨j,hj⟩ := by
  revert hi hj
  induction hij with
  | refl => intro hi hj; exact Relation.ReflTransGen.refl
  | @tail j k hij hjk ih =>
    intro hi hk
    have hj := reaches_mem_of_final P W hW hi hij
    exact Relation.ReflTransGen.tail (ih hi hj) hjk

lemma class_image_final {n : Type*} [DecidableEq n] (P : Matrix n n ℝ) (W : Finset n)
    (hW : IsFinal P W) (U : Finset W) (hU : IsClass (block P W) U) :
    IsClass P (U.image Subtype.val) := by
  classical
  obtain ⟨a,ha,h⟩ := hU
  refine ⟨a,Finset.mem_image.mpr ⟨a,ha,rfl⟩,?_⟩
  intro j
  constructor
  · rintro hj
    obtain ⟨j',hj',rfl⟩ := Finset.mem_image.mp hj
    exact ⟨block_reaches P W ((h j').mp hj').1,block_reaches P W ((h j').mp hj').2⟩
  · rintro ⟨haj,hja⟩
    have hjW := reaches_mem_of_final P W hW a.property haj
    let j' : W := ⟨j,hjW⟩
    have hjU : j' ∈ U := (h j').mpr
      ⟨reaches_restrict_final P W hW haj a.property hjW,
       reaches_restrict_final P W hW hja hjW a.property⟩
    exact Finset.mem_image.mpr ⟨j',hjU,rfl⟩

lemma final_of_image_final {n : Type*} [DecidableEq n] (P : Matrix n n ℝ)
    (W : Finset n) (U : Finset W) (hT : IsFinal P (U.image Subtype.val)) :
    IsFinal (block P W) U := by
  intro i hi j hj
  apply hT i (Finset.mem_image.mpr ⟨i,hi,rfl⟩) j
  intro h
  obtain ⟨k,hk,hkj⟩ := Finset.mem_image.mp h
  exact hj ((Subtype.val_injective hkj) ▸ hk)

lemma specRad_submatrix_equiv {n m : Type*} [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m] (P : Matrix n n ℝ) (e : m ≃ n) :
    specRad (P.submatrix e e)=specRad P := by
  unfold specRad spectralRadius
  have he : (P.submatrix e e).map (algebraMap ℝ ℂ) =
      Matrix.reindexAlgEquiv ℂ ℂ e.symm (P.map (algebraMap ℝ ℂ)) := rfl
  rw [he,AlgEquiv.spectrum_eq]

noncomputable def blockImageEquiv {n : Type*} [DecidableEq n] (W : Finset n) (U : Finset W) :
    U ≃ U.image (Subtype.val : W → n) := by
  classical
  apply Equiv.ofBijective (fun u : U => ⟨u.1.1,Finset.mem_image.mpr ⟨u.1,u.2,rfl⟩⟩)
  constructor
  · intro u v h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun t : U.image (Subtype.val : W → n) => (t : n)) h
  · intro t
    obtain ⟨u,hu,he⟩ := Finset.mem_image.mp t.property
    exact ⟨⟨u,hu⟩,Subtype.ext he⟩

lemma nested_block_specRad {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (W : Finset n) (U : Finset W) :
    specRad (block (block P W) U)=specRad (block P (U.image Subtype.val)) := by
  classical
  have he : block (block P W) U = (block P (U.image Subtype.val)).submatrix
      (blockImageEquiv W U) (blockImageEquiv W U) := rfl
  rw [he,specRad_submatrix_equiv]

end SaturatedNet.Uniqueness.NonexpansiveProof

-- Subcritical

set_option maxHeartbeats 0

open Matrix Filter
open scoped Topology Matrix.Norms.Operator

namespace SaturatedNet.Uniqueness.NonexpansiveProof

lemma exists_pow_norm_lt_one {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hr : specRad P < 1) :
    ∃ N : ℕ, 0 < N ∧ ‖(P.map (algebraMap ℝ ℂ)) ^ N‖ < 1 := by
  have hlim := spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius
    (P.map (algebraMap ℝ ℂ))
  have hev := hlim.eventually (gt_mem_nhds hr)
  obtain ⟨N, hroot, hN⟩ := (hev.and (eventually_gt_atTop 0)).exists
  refine ⟨N, hN, ?_⟩
  have hroot' : ‖P.map (algebraMap ℝ ℂ) ^ N‖ ^ (1 / (N : ℝ)) < 1 := by
    apply (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1)).1
    simpa only [ENNReal.ofReal_one] using hroot
  exact (Real.rpow_lt_one_iff' (norm_nonneg _) (one_div_pos.mpr (by exact_mod_cast hN))).1 hroot'

lemma subcritical_supersolution {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j) (hr : specRad P < 1)
    (b : n → ℝ) : ∃ v : n → ℝ, (∀ i, 0 < v i) ∧ P *ᵥ v + b ≤ v := by
  classical
  obtain ⟨N, hN, hnorm⟩ := exists_pow_norm_lt_one P hr
  let r : ℝ := ‖P.map (algebraMap ℝ ℂ) ^ N‖
  have hrpos : 0 < 1 - r := sub_pos.mpr hnorm
  have hrows (i : n) : ∑ j, (P ^ N) i j ≤ r := by
    have hrow : (∑ j, ‖(P.map (algebraMap ℝ ℂ) ^ N) i j‖) ≤ r := by
      dsimp only [r]
      rw [Matrix.linfty_opNorm_def]
      have hnn := (Finset.le_sup (s := Finset.univ)
        (f := fun i => ∑ j, ‖(P.map (algebraMap ℝ ℂ) ^ N) i j‖₊)
        (Finset.mem_univ i))
      simpa only [NNReal.coe_sum, coe_nnnorm] using (NNReal.coe_le_coe.mpr hnn)
    simpa only [← Matrix.map_pow P (algebraMap ℝ ℂ), Matrix.map_apply,
      norm_algebraMap, norm_one, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (Matrix.pow_apply_nonneg hP N _ _)] using hrow
  let S : Matrix n n ℝ := ∑ j ∈ Finset.range N, P ^ j
  let u : n → ℝ := S *ᵥ (fun _ => 1)
  have hu (i : n) : 1 ≤ u i := by
    have hs (j : n) : (1 : Matrix n n ℝ) i j ≤ S i j := by
      have := Finset.single_le_sum
        (f := fun l => (P ^ l) i j)
        (fun l (_hl : l ∈ Finset.range N) => Matrix.pow_apply_nonneg hP l i j)
        (Finset.mem_range.mpr hN)
      simpa [S, Matrix.sum_apply] using this
    calc
      1 = ((1 : Matrix n n ℝ) *ᵥ (fun _ => (1 : ℝ))) i := by simp
      _ ≤ u i := by
        simp only [u, Matrix.mulVec, dotProduct, mul_one]
        exact Finset.sum_le_sum fun j _ => hs j
  have hgeom : u - P *ᵥ u = (fun _ => 1) - (P ^ N) *ᵥ (fun _ => 1) := by
    have hmat : S - P * S = 1 - P ^ N := by
      simpa only [sub_mul, one_mul] using mul_neg_geom_sum P N
    dsimp only [u]
    rw [Matrix.mulVec_mulVec, ← Matrix.sub_mulVec, hmat,
      Matrix.sub_mulVec, Matrix.one_mulVec]
  have hmargin (i : n) : 1 - r ≤ u i - (P *ᵥ u) i := by
    have h := congrFun hgeom i
    simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, mul_one] at h
    have hi := hrows i
    change 1 - r ≤ u i - ∑ j, P i j * u j
    linarith
  let B : ℝ := ‖b‖ + 1
  let t : ℝ := B / (1 - r)
  have hB : 0 < B := by dsimp only [B]; positivity
  have ht : 0 < t := div_pos hB hrpos
  have htb : t * (1 - r) = B := div_mul_cancel₀ B (ne_of_gt hrpos)
  refine ⟨t • u, fun i => ?_, ?_⟩
  · change 0 < t * u i
    exact mul_pos ht (lt_of_lt_of_le zero_lt_one (hu i))
  · intro i
    simp only [Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hi : b i ≤ B := by
      exact (le_abs_self (b i)).trans ((norm_le_pi_norm b i).trans (by dsimp only [B]; linarith))
    have hm := mul_le_mul_of_nonneg_left (hmargin i) ht.le
    nlinarith

end SaturatedNet.Uniqueness.NonexpansiveProof


-- Backward

open Matrix
namespace SaturatedNet.Uniqueness.NonexpansiveProof
universe u

lemma backward_aux
    (hpf : ∀ {m : Type u} [Fintype m] [DecidableEq m]
      (A : Matrix m m ℝ), (∀ i j, 0 ≤ A i j) →
      (Nonempty m → ∃ p π : m → ℝ, 0 ≤ p ∧ p ≠ 0 ∧ 0 ≤ π ∧ π ≠ 0 ∧
        A *ᵥ p = (specRad A).toReal • p ∧ π ᵥ* A = (specRad A).toReal • π) ∧
      ∀ S : Finset m, specRad (block A S) ≤ specRad A)
    (N : ℕ) : ∀ {n : Type u} [Fintype n] [DecidableEq n], Fintype.card n = N →
    ∀ (P : Matrix n n ℝ), (∀ i j, 0 ≤ P i j) → specRad P ≤ 1 →
    (∀ V : Finset n, IsClass P V → specRad (block P V)=1 → IsFinal P V) →
    ∃ v : n → ℝ, (∀ i, 0 < v i) ∧ P*ᵥv≤v := by
  classical
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro n _ _ hn P hP hr hfinal
    cases isEmpty_or_nonempty n with
    | inl he =>
      let := he
      exact ⟨fun _ => 1, fun i => isEmptyElim i, fun i => isEmptyElim i⟩
    | inr he =>
      let := he
      obtain ⟨V,hV,hsource⟩ := exists_source_class P
      let W : Finset n := Vᶜ
      have hW : IsFinal P W := by
        intro i hi j hj
        exact hsource i (Finset.mem_compl.mp hi) j (by simpa [W] using hj)
      have hcard : Fintype.card W < N := by
        rw [← hn,Fintype.card_coe]
        have hVpos : 0 < V.card := Finset.card_pos.mpr ⟨hV.choose,hV.choose_spec.1⟩
        have hsum : W.card + V.card = Fintype.card n := by
          dsimp only [W]
          simp
        omega
      have hrW : specRad (block P W) ≤ 1 := ((hpf P hP).2 W).trans hr
      have hfinalW : ∀ U : Finset W, IsClass (block P W) U →
          specRad (block (block P W) U)=1 → IsFinal (block P W) U := by
        intro U hU hcrit
        apply final_of_image_final P W U
        apply hfinal _ (class_image_final P W hW U hU)
        rwa [nested_block_specRad] at hcrit
      obtain ⟨vW,hvW,hPW⟩ := ih (Fintype.card W) hcard rfl (block P W)
        (fun i j => hP i j) hrW hfinalW
      let b : V → ℝ := fun i => ∑ j : W, P i j*vW j
      have hrV : specRad (block P V) ≤ 1 := ((hpf P hP).2 V).trans hr
      have hVsol : ∃ vV : V → ℝ, (∀ i, 0 < vV i) ∧ block P V*ᵥvV+b≤vV := by
        rcases lt_or_eq_of_le hrV with hlt|heq
        · exact subcritical_supersolution (block P V) (fun i j => hP i j) hlt b
        · have hb : b=0 := by
            funext i
            apply Finset.sum_eq_zero
            intro j _
            rw [hfinal V hV heq i i.property j (Finset.mem_compl.mp j.property),zero_mul]
          have hneV : Nonempty V := ⟨⟨hV.choose,hV.choose_spec.1⟩⟩
          obtain ⟨v,π,hv,hvne,_,_,hev,_⟩ := (hpf (block P V) (fun i j => hP i j)).1 hneV
          have hvpos := eigenvector_pos_on_class P hP V hV v hv hvne _ hev
          refine ⟨v,hvpos,?_⟩
          rw [hb,add_zero,hev,heq]
          simp
      obtain ⟨vV,hvV,hPV⟩ := hVsol
      let v : n → ℝ := fun i => if hi : i∈V then vV ⟨i,hi⟩ else vW ⟨i,Finset.mem_compl.mpr hi⟩
      have hvV' (i : V) : v i=vV i := by simp [v,i.property]
      have hvW' (i : W) : v i=vW i := by simp [v,Finset.mem_compl.mp i.property]
      refine ⟨v,?_,?_⟩
      · intro i
        dsimp only [v]
        split_ifs with hi
        · exact hvV ⟨i,hi⟩
        · exact hvW ⟨i,Finset.mem_compl.mpr hi⟩
      · intro i
        rw [row_split P V v i]
        by_cases hi : i∈V
        · have h := hPV ⟨i,hi⟩
          simpa only [Pi.add_apply,Matrix.mulVec,dotProduct,block,Matrix.submatrix_apply,
            b,hvV',hvW',hvV' ⟨i,hi⟩] using h
        · have hz : (∑ j : V, P i j*v j)=0 := by
            apply Finset.sum_eq_zero
            intro j _
            rw [hsource i hi j j.property,zero_mul]
          rw [hz,zero_add,hvW' ⟨i,Finset.mem_compl.mpr hi⟩]
          simpa only [Matrix.mulVec,dotProduct,block,Matrix.submatrix_apply,hvW'] using
            hPW ⟨i,Finset.mem_compl.mpr hi⟩

end SaturatedNet.Uniqueness.NonexpansiveProof

open SaturatedNet.Uniqueness

theorem solution {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j) :
    (∃ v : n → ℝ, (∀ i, 0 < v i) ∧ P *ᵥ v ≤ v) ↔
      (specRad P < 1 ∨
        (specRad P = 1 ∧ ∀ V : Finset n, IsClass P V → IsBasic P V → IsFinal P V)) := by
  constructor
  · rintro ⟨v,hv,hPv⟩
    exact NonexpansiveProof.forward P hP v hv hPv
  · rintro (hr|⟨hr,hfinal⟩)
    · obtain ⟨v,hv,hPv⟩ := NonexpansiveProof.subcritical_supersolution P hP hr 0
      exact ⟨v,hv,by simpa using hPv⟩
    · apply NonexpansiveProof.backward_aux
        (fun A hA => proposition_2_i_ii A hA) (Fintype.card n) rfl P hP hr.le
      intro V hV hcrit
      exact hfinal V hV (hcrit.trans hr.symm)
