-- Prove2me | solution 1 for VRPTWColGen92.Bound.colgen_certificate
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-18T08:47:38.333589+00:00
-- url     : https://prove2.me/submissions/7f31d15b-3cc6-4ff3-849b-20003dd6be5e

-- Licensed under Apache 2.0. Complete VRPTW column-generation certificate.
import Mathlib
import Definitions.Def_VRPTWColGen92_Bound_Network
import Definitions.Def_VRPTWColGen92_Bound_CoveringLP


namespace VRPTWProof
open Finset

variable {ι E : Type*} [DecidableEq ι] [AddCommGroup E] [Module ℝ E]

omit [DecidableEq ι] in
lemma positive_relation {v : ι → E} {s : Finset ι}
    (hs : ¬ LinearIndepOn ℝ v (s : Set ι)) :
    ∃ d : ι → ℝ, (∑ i ∈ s, d i • v i) = 0 ∧ ∃ i ∈ s, 0 < d i := by
  classical
  rw [linearIndepOn_finset_iff] at hs
  push Not at hs
  obtain ⟨d, hd, i, hi, hdi⟩ := hs
  by_cases hp : ∃ j ∈ s, 0 < d j
  · exact ⟨d, hd, hp⟩
  · refine ⟨fun j => -d j, ?_, i, hi, ?_⟩
    · simp only [neg_smul, sum_neg_distrib, hd, neg_zero]
    · have hn : ¬ 0 < d i := fun h => hp ⟨i, hi, h⟩
      exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hn) hdi)

lemma cone_erase {v : ι → E} {s : Finset ι} {a : ι → ℝ}
    (ha : ∀ i ∈ s, 0 ≤ a i) (hs : ¬ LinearIndepOn ℝ v (s : Set ι)) :
    ∃ j ∈ s, ∃ b : ι → ℝ, (∀ i ∈ s.erase j, 0 ≤ b i) ∧
      (∑ i ∈ s.erase j, b i • v i) = ∑ i ∈ s, a i • v i := by
  classical
  obtain ⟨d, hd, hp⟩ := positive_relation hs
  let t := s.filter (fun i => 0 < d i)
  have ht : t.Nonempty := by
    obtain ⟨i, hi, hdi⟩ := hp
    exact ⟨i, mem_filter.mpr ⟨hi, hdi⟩⟩
  obtain ⟨j, hj, hmin⟩ := t.exists_min_image (fun i => a i / d i) ht
  have hjs : j ∈ s := (mem_filter.mp hj).1
  have hdj : 0 < d j := (mem_filter.mp hj).2
  let b : ι → ℝ := fun i => a i - (a j / d j) * d i
  have hb0 : b j = 0 := by simp [b, hdj.ne']
  refine ⟨j, hjs, b, ?_, ?_⟩
  · intro i hi
    have his : i ∈ s := mem_of_mem_erase hi
    change 0 ≤ a i - (a j / d j) * d i
    rw [sub_nonneg]
    by_cases hdi : 0 < d i
    · exact (le_div_iff₀ hdi).mp (hmin i (mem_filter.mpr ⟨his, hdi⟩))
    · exact (mul_nonpos_of_nonneg_of_nonpos
        (div_nonneg (ha j hjs) hdj.le) (le_of_not_gt hdi)).trans (ha i his)
  · calc
      (∑ i ∈ s.erase j, b i • v i) = ∑ i ∈ s, b i • v i := by
        exact sum_erase _ (by simp [hb0])
      _ = ∑ i ∈ s, a i • v i := by
        simp only [b, sub_smul, mul_smul, sum_sub_distrib, ← smul_sum, hd,
          smul_zero, sub_zero]

lemma independent_cone_representation (v : ι → E) (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) :
    ∃ t ⊆ s, ∃ b : ι → ℝ, LinearIndepOn ℝ v (t : Set ι) ∧
      (∀ i ∈ t, 0 ≤ b i) ∧ (∑ i ∈ t, b i • v i) = ∑ i ∈ s, a i • v i := by
  classical
  induction s using Finset.strongInductionOn generalizing a
  rename_i s ih
  by_cases hs : LinearIndepOn ℝ v (s : Set ι)
  · exact ⟨s, Subset.rfl, a, hs, ha, rfl⟩
  · obtain ⟨j, hj, b, hb, he⟩ := cone_erase ha hs
    obtain ⟨t, ht, c, hc, hcn, hce⟩ := ih (s.erase j) (erase_ssubset hj) b hb
    exact ⟨t, ht.trans (erase_subset _ _), c, hc, hcn, hce.trans he⟩

end VRPTWProof


namespace VRPTWProof
open Finset Set

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def finiteCone (v : ι → E) : Set E :=
  {x | ∃ a : ι → ℝ, (∀ i, 0 ≤ a i) ∧ (∑ i, a i • v i) = x}

def subsetCone (v : ι → E) (s : Finset ι) : Set E :=
  (Fintype.linearCombination ℝ (fun i : s => v i)) '' {a : s → ℝ | ∀ i, 0 ≤ a i}

omit [DecidableEq ι] in
lemma subsetCone_closed (v : ι → E) (s : Finset ι)
    (hs : LinearIndepOn ℝ v (s : Set ι)) : IsClosed (subsetCone v s) := by
  have hc : IsClosed {a : s → ℝ | ∀ i, 0 ≤ a i} := by
    have he : {a : s → ℝ | ∀ i, 0 ≤ a i} = ⋂ i, {a : s → ℝ | 0 ≤ a i} := by ext; simp
    rw [he]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  exact (LinearMap.isClosedEmbedding_of_injective
    (LinearMap.ker_eq_bot.mpr hs.linearIndependent.fintypeLinearCombination_injective)).isClosedMap _ hc

lemma finiteCone_eq_union (v : ι → E) :
    finiteCone v = ⋃ s : {s : Finset ι // LinearIndepOn ℝ v (s : Set ι)},
      subsetCone v s.1 := by
  classical
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨s, _, b, hs, hb, he⟩ := independent_cone_representation v univ a
      (fun i _ => ha i)
    refine mem_iUnion.mpr ⟨⟨s, hs⟩, ?_⟩
    refine ⟨fun i => b i, fun i => hb i i.2, ?_⟩
    rw [← Finset.sum_attach s] at he
    exact he
  · intro hx
    obtain ⟨s, b, hb, he⟩ := mem_iUnion.mp hx
    let a : ι → ℝ := fun i => if hi : i ∈ s.1 then b ⟨i, hi⟩ else 0
    refine ⟨a, ?_, ?_⟩
    · intro i
      dsimp [a]
      split_ifs with hi
      · exact hb ⟨i, hi⟩
      · exact le_rfl
    · rw [← he]
      simp only [Fintype.linearCombination_apply]
      calc
        (∑ i, a i • v i) = ∑ i ∈ s.1, a i • v i := by
          symm
          apply sum_subset (subset_univ _)
          intro i _ hi
          simp [a, hi]
        _ = ∑ i : s.1, b i • v i := by
          rw [← Finset.sum_coe_sort]
          apply sum_congr rfl
          intro i _
          simp [a, i.2]

lemma finiteCone_closed (v : ι → E) : IsClosed (finiteCone v) := by
  classical
  rw [finiteCone_eq_union]
  exact isClosed_iUnion_of_finite fun s => subsetCone_closed v s.1 s.2

noncomputable def finiteProperCone (v : ι → E) : ProperCone ℝ E where
  carrier := finiteCone v
  zero_mem' := ⟨0, by simp, by simp⟩
  add_mem' := by
    rintro x y ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    refine ⟨fun i => a i + b i, fun i => add_nonneg (ha i) (hb i), ?_⟩
    simp only [add_smul, sum_add_distrib]
  smul_mem' := by
    rintro c x ⟨a, ha, rfl⟩
    refine ⟨fun i => (c : ℝ) * a i, fun i => mul_nonneg c.2 (ha i), ?_⟩
    simp only [mul_smul, Finset.smul_sum]
    rfl
  isClosed' := finiteCone_closed v

end VRPTWProof


namespace VRPTWProof
open Finset

variable {R C : Type*} [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]

def lpGenerator (A : R → C → ℝ) (c : C → ℝ) : C ⊕ (R ⊕ Unit) → (R → ℝ) × ℝ
  | .inl j => (fun i => A i j, c j)
  | .inr (.inl i) => (-Pi.single i 1, 0)
  | .inr (.inr _) => (0, 1)

omit [DecidableEq C] in
lemma lp_generator_sum (A : R → C → ℝ) (c : C → ℝ)
    (a : C ⊕ (R ⊕ Unit) → ℝ) :
    (∑ k, a k • lpGenerator A c k) =
      ((fun i => (∑ j, A i j * a (.inl j)) - a (.inr (.inl i))),
        (∑ j, c j * a (.inl j)) + a (.inr (.inr ()))) := by
  ext i
  · simp only [Fintype.sum_sum_type, lpGenerator, Prod.fst_add, Prod.fst_sum,
      Prod.smul_fst, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.neg_apply, Fintype.sum_unique, Pi.zero_apply, mul_zero, add_zero]
    simp only [Pi.single_apply]
    simp only [mul_ite, mul_one, mul_zero, mul_neg, sum_neg_distrib,
      sum_ite_eq, mem_univ, if_true]
    congr 1
    apply sum_congr rfl
    intro j _
    ring
  · simp only [Fintype.sum_sum_type, lpGenerator, Prod.snd_add, Prod.snd_sum,
      Prod.smul_snd, smul_eq_mul, mul_zero, sum_const_zero, Fintype.sum_unique,
      mul_one, zero_add]
    congr 1
    apply sum_congr rfl
    intro j _
    ring

lemma lp_cone_mem (A : R → C → ℝ) (c : C → ℝ) (u : R → ℝ) (v : ℝ) :
    (u, v) ∈ finiteProperCone (lpGenerator A c) ↔
      ∃ x : C → ℝ, (∀ j, 0 ≤ x j) ∧ (∀ i, u i ≤ ∑ j, A i j * x j) ∧
        (∑ j, c j * x j) ≤ v := by
  classical
  change (∃ a : C ⊕ (R ⊕ Unit) → ℝ, (∀ k, 0 ≤ a k) ∧ (∑ k, a k • lpGenerator A c k) = (u,v)) ↔ _
  constructor
  · rintro ⟨a, ha, he⟩
    rw [lp_generator_sum] at he
    refine ⟨fun j => a (.inl j), fun j => ha _, ?_, ?_⟩
    · intro i
      have hi := congrArg (fun p : (R → ℝ) × ℝ => p.1 i) he
      dsimp at hi
      linarith [ha (.inr (.inl i))]
    · have hi := congrArg Prod.snd he
      dsimp at hi
      linarith [ha (.inr (.inr ()))]
  · rintro ⟨x, hx, hu, hv⟩
    let a : C ⊕ (R ⊕ Unit) → ℝ := Sum.elim x
      (Sum.elim (fun i => (∑ j, A i j * x j) - u i) (fun _ => v - ∑ j, c j * x j))
    refine ⟨a, ?_, ?_⟩
    · intro k
      rcases k with j | (i | t)
      · exact hx j
      · exact sub_nonneg.mpr (hu i)
      · exact sub_nonneg.mpr hv
    · rw [lp_generator_sum]
      ext i <;> simp [a]

lemma finite_lp_approx_dual (A : R → C → ℝ) (b : R → ℝ) (c : C → ℝ)
    (x : C → ℝ) (hx : ∀ j, 0 ≤ x j) (hAx : ∀ i, b i ≤ ∑ j, A i j * x j)
    (hopt : ∀ z : C → ℝ, (∀ j, 0 ≤ z j) → (∀ i, b i ≤ ∑ j, A i j * z j) →
      (∑ j, c j * x j) ≤ ∑ j, c j * z j)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ y : R → ℝ, (∀ i, 0 ≤ y i) ∧ (∀ j, (∑ i, A i j * y i) ≤ c j) ∧
      (∑ j, c j * x j) - ε < ∑ i, b i * y i := by
  classical
  let v := ∑ j, c j * x j
  have hout : (b, v-ε) ∉ finiteProperCone (lpGenerator A c) := by
    rw [lp_cone_mem]
    rintro ⟨z, hz, hAz, hcz⟩
    have := hopt z hz hAz
    dsimp [v] at hcz
    linarith
  obtain ⟨f, hf, hneg⟩ := (finiteProperCone (lpGenerator A c)).hyperplane_separation_point hout
  let r : ℝ := f (0,1)
  let l : R → ℝ := fun i => -f (Pi.single i 1,0)
  have hform (u : R → ℝ) (t : ℝ) : f (u,t) = -(∑ i, u i*l i) + t*r := by
    have he : (u,t) = (∑ i, u i • (Pi.single i 1, (0 : ℝ))) + t • (0, (1 : ℝ)) := by
      ext i <;> simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
    rw [he, map_add, map_sum, map_smul]
    simp only [map_smul, smul_eq_mul, l, r, mul_neg, sum_neg_distrib, neg_neg]
  have hgen (k : C ⊕ (R ⊕ Unit)) : 0 ≤ f (lpGenerator A c k) := by
    apply hf
    refine ⟨(Pi.single k (1 : ℝ) : C ⊕ (R ⊕ Unit) → ℝ), ?_, ?_⟩
    · intro j
      simp only [Pi.single_apply]
      split_ifs <;> norm_num
    · simp
  have hl (i : R) : 0 ≤ l i := by
    have h := hgen (.inr (.inl i))
    change 0 ≤ f (-Pi.single i 1,0) at h
    have he : (-(Pi.single i (1 : ℝ) : R → ℝ), (0 : ℝ)) = -(Pi.single i 1,0) := by simp
    rwa [he, map_neg] at h
  have hp := hf (b,v) ((lp_cone_mem A c b v).mpr ⟨x,hx,hAx,le_rfl⟩)
  rw [hform] at hp hneg
  have hr : 0 < r := by nlinarith
  refine ⟨fun i => l i / r, fun i => div_nonneg (hl i) hr.le, ?_, ?_⟩
  · intro j
    have h := hgen (.inl j)
    change 0 ≤ f ((fun i => A i j), c j) at h
    rw [hform] at h
    change (∑ i, A i j * (l i / r)) ≤ c j
    simp_rw [← mul_div_assoc]
    rw [← sum_div, div_le_iff₀ hr]
    nlinarith
  · change v - ε < ∑ i, b i * (l i / r)
    simp_rw [← mul_div_assoc]
    rw [← sum_div, lt_div_iff₀ hr]
    nlinarith

end VRPTWProof


namespace VRPTWProof
open Finset

variable {R C : Type*} [Fintype R] [Fintype C]

lemma finite_lp_weak_duality (A : R → C → ℝ) (b : R → ℝ) (c : C → ℝ)
    (x : C → ℝ) (y : R → ℝ)
    (hx : ∀ j, 0 ≤ x j) (hAx : ∀ i, b i ≤ ∑ j, A i j * x j)
    (hy : ∀ i, 0 ≤ y i) (hAy : ∀ j, (∑ i, A i j * y i) ≤ c j) :
    (∑ i, b i * y i) ≤ ∑ j, c j * x j := by
  calc
    (∑ i, b i * y i) ≤ ∑ i, (∑ j, A i j * x j) * y i :=
      sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hAx i) (hy i)
    _ = ∑ j, (∑ i, A i j * y i) * x j := by
      simp only [sum_mul]
      rw [sum_comm]
      apply sum_congr rfl
      intro j _
      apply sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ j, c j * x j :=
      sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hAy j) (hx j)

lemma finite_lp_zero_gap (A : R → C → ℝ) (b : R → ℝ) (c : C → ℝ)
    (x : C → ℝ) (y : R → ℝ)
    (hx : ∀ j, 0 ≤ x j) (hAx : ∀ i, b i ≤ ∑ j, A i j * x j)
    (hopt : ∀ z : C → ℝ, (∀ j, 0 ≤ z j) → (∀ i, b i ≤ ∑ j, A i j * z j) →
      (∑ j, c j * x j) ≤ ∑ j, c j * z j)
    (hy : ∀ i, 0 ≤ y i) (hAy : ∀ j, (∑ i, A i j * y i) ≤ c j)
    (hdopt : ∀ w : R → ℝ, (∀ i, 0 ≤ w i) → (∀ j, (∑ i, A i j * w i) ≤ c j) →
      (∑ i, b i * w i) ≤ ∑ i, b i * y i) :
    (∑ j, c j * x j) = ∑ i, b i * y i := by
  classical
  apply le_antisymm _ (finite_lp_weak_duality A b c x y hx hAx hy hAy)
  by_contra! h
  obtain ⟨w, hw, hAw, hv⟩ := finite_lp_approx_dual A b c x hx hAx hopt
    ((∑ j, c j * x j) - ∑ i, b i * y i) (sub_pos.mpr h)
  have := hdopt w hw hAw
  linarith

end VRPTWProof


noncomputable section
namespace VRPTWProof
open VRPTWColGen92.Bound Finset
variable {n : ℕ}

theorem source_sum (f : Fin (n+1) → ℝ) (a : Fin (n+1))
    (p : List (Fin (n+1))) :
    ((((a :: p) ++ [0]).zip ((a :: p) ++ [0]).tail).map (fun e : Fin (n+1) × Fin (n+1) => f e.1)).sum =
      f a + (p.map f).sum := by
  induction p generalizing a with
  | nil => simp
  | cons b p ih =>
    simpa only [List.cons_append, List.tail_cons, List.zip_cons_cons, List.map_cons,
      List.sum_cons, add_assoc] using congrArg (fun x => f a + x) (ih b)

theorem weighted_counts {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → ℝ) (p : List α) :
    (p.map f).sum = ∑ i, f i * (p.count i : ℝ) := by
  induction p with
  | nil => simp
  | cons a p ih =>
    simp only [List.map_cons, List.sum_cons, List.count_cons, Nat.cast_add,
      mul_add, Finset.sum_add_distrib]
    simp only [ih]
    simp [add_comm]

theorem path_pricing_identity (I : Instance n) (y : DualPoint n)
    (p : List (Fin (n+1))) (hp : (0 : Fin (n+1)) ∉ p) :
    pathMarginal I y p = columnMarginal I y p := by
  have hs := source_sum (nodeDual y) 0 p
  have hc : (p.map (nodeDual y)).sum =
      ∑ i ∈ Finset.univ.erase (0 : Fin (n+1)), y.π i * (p.count i : ℝ) := by
    rw [weighted_counts]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : Fin (n+1)))]
    have hz : p.count (0 : Fin (n+1)) = 0 := List.count_eq_zero.mpr hp
    simp only [hz, Nat.cast_zero, mul_zero, add_zero]
    apply Finset.sum_congr rfl
    intro i hi
    simp [nodeDual, (Finset.mem_erase.mp hi).1]
  have hl (l : List (Fin (n+1) × Fin (n+1))) :
      (l.map (fun e => (1-y.πc)*I.c e.1 e.2-nodeDual y e.1)).sum =
      (1-y.πc)*(l.map (fun e => I.c e.1 e.2)).sum -
        (l.map (fun e => nodeDual y e.1)).sum := by
    induction l with
    | nil => simp
    | cons e l ih => simp only [List.map_cons, List.sum_cons, ih]; ring
  unfold pathMarginal arcMarginal columnMarginal cost arcSum
  rw [hl]
  change (1-y.πc) * arcSum I.c p -
    (((0::p)++[0]).zip ((0::p)++[0]).tail |>.map (fun e : Fin (n+1) × Fin (n+1) => nodeDual y e.1)).sum = _
  rw [hs, hc]
  simp only [nodeDual, if_true, arcSum]
  ring

end VRPTWProof


noncomputable section
namespace VRPTWProof
open VRPTWColGen92.Bound Finset
variable {n : ℕ}

theorem route_is_path3 (I : Instance n) (p : List (Fin (n+1)))
    (hp : IsRoute I p) : IsPath3 I p := by
  refine ⟨hp.1, ?_⟩
  intro k hk he
  have hinj : Function.Injective p.get := List.nodup_iff_injective_get.mp hp.2
  have h : (⟨k, by omega⟩ : Fin p.length) = ⟨k+2,hk⟩ := hinj he
  have hv : k = k+2 := congrArg Fin.val h
  omega

theorem path_cost_nonneg (I : Instance n) (p : List (Fin (n+1)))
    (hp : ArcsOK I p) (hc : ∀ i j, I.arc i j → 0 ≤ I.c i j) : 0 ≤ cost I p := by
  unfold cost arcSum
  apply List.sum_nonneg
  intro v hv
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hv
  obtain ⟨k,hk⟩ := List.mem_iff_get.mp he
  have hlen : k.val + 1 < (nodes p).length := by
    have := k.isLt
    simp only [List.length_zip, List.length_tail] at this
    omega
  have heq : e = ((nodes p)[k.val], (nodes p)[k.val+1]) := by
    rw [← hk]
    simp
  rw [heq]
  exact hc _ _ (hp k.val hlen)

end VRPTWProof


noncomputable section
namespace VRPTWProof
open VRPTWColGen92.Bound Finset
variable {n : ℕ}

theorem native_weak_duality (I : Instance n) (R : Set (List (Fin (n+1))))
    (z : LPPoint n) (hz : LPFeasible I R z) (y : DualPoint n)
    (hπ : ∀ i : Fin (n+1), i ≠ 0 → 0 ≤ y.π i) (hd : 0 ≤ y.πd) (hc : 0 ≤ y.πc)
    (hcol : ∀ p ∈ R,
      (∑ i ∈ univ.erase (0 : Fin (n+1)), y.π i * (p.count i : ℝ)) +
        y.πd + y.πc * cost I p ≤ cost I p) :
    dualObjective y ≤ objective I z := by
  classical
  rcases hz with ⟨hsupp,hx,hcover,hxd,hxc,hxd0,hxc0⟩
  have hcover' : dualObjective y ≤ ∑ p ∈ z.x.support,
      (∑ i ∈ univ.erase (0 : Fin (n+1)), y.π i * (p.count i : ℝ)) * z.x p := by
    unfold dualObjective
    calc
      _ ≤ ∑ i ∈ univ.erase (0 : Fin (n+1)), y.π i *
          (∑ p ∈ z.x.support, (p.count i : ℝ) * z.x p) := by
        apply sum_le_sum
        intro i hi
        simpa using mul_le_mul_of_nonneg_left (hcover i (mem_erase.mp hi).1)
          (hπ i (mem_erase.mp hi).1)
      _ = _ := by
        simp_rw [mul_sum, ← mul_assoc]
        rw [sum_comm]
        simp_rw [sum_mul]
  have h := sum_le_sum (fun p hp =>
    mul_le_mul_of_nonneg_right (hcol p (hsupp p hp)) (hx p))
  have he : (∑ p ∈ z.x.support,
      ((∑ i ∈ univ.erase (0 : Fin (n+1)), y.π i * (p.count i : ℝ)) +
        y.πd + y.πc * cost I p) * z.x p) =
      (∑ p ∈ z.x.support,
        (∑ i ∈ univ.erase (0 : Fin (n+1)), y.π i * (p.count i : ℝ)) * z.x p) +
      y.πd*z.Xd + y.πc*z.Xc := by
    simp_rw [add_mul, sum_add_distrib, mul_assoc]
    rw [← mul_sum, ← mul_sum, hxd, hxc]
  rw [he] at h
  change _ ≤ objective I z at h
  have hdn := mul_nonneg hd hxd0
  have hcn := mul_nonneg hc hxc0
  linarith

end VRPTWProof


noncomputable section
namespace VRPTWProof
open VRPTWColGen92.Bound Finset
variable {n : ℕ}

def columnWeights (R : Finset (List (Fin (n+1)))) (x : R → ℝ) :
    List (Fin (n+1)) →₀ ℝ :=
  Finsupp.onFinset R (fun p => if h : p ∈ R then x ⟨p,h⟩ else 0)
    (by intro p hp; by_contra h; simp [h] at hp)

theorem columnWeights_apply (R : Finset (List (Fin (n+1)))) (x : R → ℝ)
    (p : List (Fin (n+1))) : columnWeights R x p = if h : p ∈ R then x ⟨p,h⟩ else 0 := rfl

theorem columnWeights_support (R : Finset (List (Fin (n+1)))) (x : R → ℝ) :
    (columnWeights R x).support ⊆ R := by
  intro p hp
  by_contra hn
  have := Finsupp.mem_support_iff.mp hp
  simp [columnWeights_apply,hn] at this

theorem support_sum_eq (R : Finset (List (Fin (n+1))))
    (w : List (Fin (n+1)) →₀ ℝ) (hw : w.support ⊆ R) (f : List (Fin (n+1)) → ℝ) :
    (∑ p ∈ w.support, f p * w p) = ∑ p : R, f p * w p := by
  classical
  have he : (∑ p ∈ w.support, f p*w p) = ∑ p ∈ R, f p*w p := by
    apply sum_subset hw
    intro p hp hn
    have hz : w p = 0 := by simpa using hn
    simp [hz]
  rw [← Finset.sum_attach R] at he
  exact he

theorem columnWeights_sum (R : Finset (List (Fin (n+1)))) (x : R → ℝ)
    (f : List (Fin (n+1)) → ℝ) :
    (∑ p ∈ (columnWeights R x).support, f p * columnWeights R x p) =
      ∑ p : R, f p * x p := by
  rw [support_sum_eq R _ (columnWeights_support R x)]
  apply sum_congr rfl
  intro p hp
  simp [columnWeights_apply,p.property]

end VRPTWProof


noncomputable section
namespace VRPTWProof
open VRPTWColGen92.Bound Finset
variable {n : ℕ}

def rowMatrix (I : Instance n) (i : Fin (n+1)) (p : List (Fin (n+1))) : ℝ :=
  if i = 0 then cost I p else p.count i

def rowRhs (i : Fin (n+1)) : ℝ := if i = 0 then 0 else 1

def columnPoint (I : Instance n) (R : Finset (List (Fin (n+1)))) (x : R → ℝ) : LPPoint n where
  x := columnWeights R x
  Xd := ∑ p : R, x p
  Xc := ∑ p : R, cost I p * x p

theorem columnPoint_objective (I : Instance n) (R : Finset (List (Fin (n+1)))) (x : R → ℝ) :
    objective I (columnPoint I R x) = ∑ p : R, cost I p*x p :=
  columnWeights_sum R x (cost I)

theorem columnPoint_feasible (I : Instance n) (R : Finset (List (Fin (n+1))))
    (x : R → ℝ) (hx : ∀ p, 0 ≤ x p)
    (hA : ∀ i, rowRhs i ≤ ∑ p : R, rowMatrix I i p * x p) :
    LPFeasible I (↑R : Set (List (Fin (n+1)))) (columnPoint I R x) := by
  classical
  refine ⟨columnWeights_support R x, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    change 0 ≤ columnWeights R x p
    rw [columnWeights_apply]
    split_ifs with h
    · exact hx ⟨p,h⟩
    · rfl
  · intro i hi
    change 1 ≤ ∑ p ∈ (columnWeights R x).support, (p.count i : ℝ)*columnWeights R x p
    rw [columnWeights_sum]
    simpa [rowRhs,rowMatrix,hi] using hA i
  · have h := columnWeights_sum R x (fun _ => 1)
    simpa [columnPoint] using h
  · exact columnWeights_sum R x (cost I)
  · exact sum_nonneg (fun p _ => hx p)
  · simpa [rowRhs,rowMatrix,columnPoint] using hA 0

theorem feasible_restrict (I : Instance n) (R : Finset (List (Fin (n+1))))
    (z : LPPoint n) (hz : LPFeasible I (↑R : Set (List (Fin (n+1)))) z) :
    (∀ p : R, 0 ≤ z.x p) ∧
    (∀ i, rowRhs i ≤ ∑ p : R, rowMatrix I i p * z.x p) ∧
    objective I z = ∑ p : R, cost I p*z.x p := by
  refine ⟨fun p => hz.2.1 p, ?_, support_sum_eq R z.x hz.1 (cost I)⟩
  intro i
  by_cases hi : i = 0
  · subst i
    simp only [rowRhs,rowMatrix,if_true]
    rw [← support_sum_eq R z.x hz.1 (cost I)]
    rw [hz.2.2.2.2.1]
    exact hz.2.2.2.2.2.2
  · simp only [rowRhs,rowMatrix,if_neg hi]
    rw [← support_sum_eq R z.x hz.1 (fun p => (p.count i : ℝ))]
    exact hz.2.2.1 i hi

def rowDual (y : DualPoint n) (i : Fin (n+1)) : ℝ := if i = 0 then y.πc else y.π i

def liftedDual (w : Fin (n+1) → ℝ) : DualPoint n where
  π := w
  πd := 0
  πc := w 0

theorem row_dual_sum (I : Instance n) (y : DualPoint n) (p : List (Fin (n+1))) :
    (∑ i, rowMatrix I i p * rowDual y i) =
    (∑ i ∈ univ.erase (0 : Fin (n+1)), y.π i * (p.count i : ℝ)) + y.πc*cost I p := by
  rw [← sum_erase_add _ _ (mem_univ (0 : Fin (n+1)))]
  simp only [rowMatrix,rowDual,if_true]
  congr 1
  · apply sum_congr rfl
    intro i hi
    simp [if_neg (mem_erase.mp hi).1,mul_comm]
  · ring

theorem row_dual_value (y : DualPoint n) :
    (∑ i, rowRhs i * rowDual y i) = dualObjective y := by
  rw [← sum_erase_add _ _ (mem_univ (0 : Fin (n+1)))]
  simp only [rowRhs,rowDual,if_true,zero_mul,add_zero,dualObjective]
  apply sum_congr rfl
  intro i hi
  simp [(mem_erase.mp hi).1]

theorem lifted_row_dual (w : Fin (n+1) → ℝ) : rowDual (liftedDual w) = w := by
  funext i
  simp only [rowDual,liftedDual]
  split_ifs with h
  · rw [h]
  · rfl

end VRPTWProof


noncomputable section
namespace VRPTWProof
open VRPTWColGen92.Bound Finset
variable {n : ℕ}

theorem integral_support_weights (I : Instance n) (z : LPPoint n)
    (hz : LPFeasible I {p | IsPath3 I p} z)
    (hint : ∀ p, ∃ m : ℕ, z.x p = m)
    (hex : ∀ i : Fin (n+1), i ≠ 0 → ∑ p ∈ z.x.support, (p.count i : ℝ)*z.x p = 1) :
    ∀ p ∈ z.x.support, z.x p = 1 ∧ p.Nodup := by
  classical
  intro p hp
  have hpath := (hz.1 p hp).1
  have hx0 := hz.2.1
  obtain ⟨m,hm⟩ := hint p
  have hm0 : 0 < m := by
    have hn := Finsupp.mem_support_iff.mp hp
    by_contra h
    have : m = 0 := by omega
    simp [this] at hm
    exact hn hm
  have hx1 : 1 ≤ z.x p := by rw [hm]; exact_mod_cast hm0
  have hterm (i : Fin (n+1)) (hi : i ≠ 0) : (p.count i : ℝ)*z.x p ≤ 1 := by
    rw [← hex i hi]
    exact single_le_sum (fun q _ => mul_nonneg (Nat.cast_nonneg _) (hx0 q)) hp
  obtain ⟨i,hi⟩ := List.exists_mem_of_ne_nil p hpath.1
  have hi0 : i ≠ 0 := by intro he; subst i; exact hpath.2.1 hi
  have hcount : (1 : ℝ) ≤ p.count i := by
    exact_mod_cast (List.count_pos_iff.mpr hi)
  have hxle : z.x p ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hcount (hx0 p)
    nlinarith [hterm i hi0]
  have hx : z.x p = 1 := le_antisymm hxle hx1
  refine ⟨hx, List.nodup_iff_count_le_one.mpr ?_⟩
  intro j
  by_cases hj : j = 0
  · subst j
    simp [List.count_eq_zero.mpr hpath.2.1]
  · have ht := hterm j hj
    rw [hx,mul_one] at ht
    exact_mod_cast ht

theorem integral_support_solution (I : Instance n) (z : LPPoint n)
    (hz : LPFeasible I {p | IsPath3 I p} z)
    (hint : ∀ p, ∃ m : ℕ, z.x p = m)
    (hex : ∀ i : Fin (n+1), i ≠ 0 → ∑ p ∈ z.x.support, (p.count i : ℝ)*z.x p = 1) :
    IsVRPTWSolution I z.x.support ∧ solCost I z.x.support = objective I z := by
  have hw := integral_support_weights I z hz hint hex
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro p hp
    exact ⟨(hz.1 p hp).1,(hw p hp).2⟩
  · intro i hi
    rw [← hex i hi]
    apply sum_congr rfl
    intro p hp
    rw [(hw p hp).1,mul_one]
  · unfold solCost objective
    apply sum_congr rfl
    intro p hp
    rw [(hw p hp).1,mul_one]

end VRPTWProof


noncomputable section
namespace VRPTWProof
open VRPTWColGen92.Bound Finset
variable {n : ℕ}

theorem native_zero_gap (I : Instance n) (R : Finset (List (Fin (n+1))))
    (z : LPPoint n) (hz : LPOptimal I (↑R : Set (List (Fin (n+1)))) z)
    (y : DualPoint n) (hy : DualOptimal I R y) : objective I z = dualObjective y := by
  classical
  obtain ⟨hx,hAx,hobj⟩ := feasible_restrict I R z hz.1
  have hdy : ∀ i, 0 ≤ rowDual y i := by
    intro i
    by_cases hi : i = 0
    · simpa [rowDual,hi] using hy.1.2.2.1
    · simpa [rowDual,hi] using hy.1.1 i hi
  have hdA : ∀ p : R, (∑ i, rowMatrix I i p * rowDual y i) ≤ cost I p := by
    intro p
    rw [row_dual_sum]
    have h := hy.1.2.2.2 p p.property
    have hd := hy.1.2.1
    linarith
  have hopt : ∀ x : R → ℝ, (∀ p, 0 ≤ x p) →
      (∀ i, rowRhs i ≤ ∑ p : R, rowMatrix I i p*x p) →
      (∑ p : R, cost I p*z.x p) ≤ ∑ p : R, cost I p*x p := by
    intro x hx' hA'
    rw [← hobj, ← columnPoint_objective I R x]
    exact hz.2 _ (columnPoint_feasible I R x hx' hA')
  have hdopt : ∀ w : Fin (n+1) → ℝ, (∀ i, 0 ≤ w i) →
      (∀ p : R, (∑ i, rowMatrix I i p*w i) ≤ cost I p) →
      (∑ i, rowRhs i*w i) ≤ ∑ i, rowRhs i*rowDual y i := by
    intro w hw hAw
    have hfeas : DualFeasible I R (liftedDual w) := by
      refine ⟨fun i _ => hw i, le_rfl, hw 0, ?_⟩
      intro p hp
      have h := hAw ⟨p,hp⟩
      rw [← lifted_row_dual w, row_dual_sum] at h
      simpa [liftedDual] using h
    have h := hy.2 _ hfeas
    rw [← row_dual_value (liftedDual w), lifted_row_dual, ← row_dual_value y] at h
    exact h
  have h := finite_lp_zero_gap (fun i (p : R) => rowMatrix I i p) rowRhs
    (fun p : R => cost I p) (fun p : R => z.x p) (rowDual y)
    hx hAx hopt hdy hdA hdopt
  simpa only [← hobj, row_dual_value] using h

end VRPTWProof


noncomputable section
namespace VRPTWProof
open VRPTWColGen92.Bound Finset
variable {n : ℕ}

theorem full_lp_optimal (I : Instance n) (R : Finset (List (Fin (n+1))))
    (hR : ∀ p ∈ R, IsPath3 I p) (z : LPPoint n)
    (hz : LPOptimal I (↑R : Set (List (Fin (n+1)))) z)
    (y : DualPoint n) (hy : DualOptimal I R y)
    (hprice : ∀ p, IsPath3 I p → 0 ≤ pathMarginal I y p) :
    LPOptimal I {p | IsPath3 I p} z := by
  refine ⟨⟨fun p hp => hR p (hz.1.1 p hp), hz.1.2⟩, ?_⟩
  intro w hw
  rw [native_zero_gap I R z hz y hy]
  apply native_weak_duality I _ w hw y hy.1.1 hy.1.2.1 hy.1.2.2.1
  intro p hp
  have h := hprice p hp
  rw [path_pricing_identity I y p hp.1.2.1] at h
  unfold columnMarginal at h
  linarith

end VRPTWProof


noncomputable section
namespace VRPTWProof
open VRPTWColGen92.Bound Finset
variable {n : ℕ}

theorem solution_lp_point (I : Instance n)
    (hc : ∀ i j, I.arc i j → 0 ≤ I.c i j)
    (S : Finset (List (Fin (n+1)))) (hS : IsVRPTWSolution I S) :
    ∃ z : LPPoint n, LPFeasible I {p | IsPath3 I p} z ∧ objective I z = solCost I S := by
  classical
  let x : S → ℝ := fun _ => 1
  have hA : ∀ i, rowRhs i ≤ ∑ p : S, rowMatrix I i p*x p := by
    intro i
    by_cases hi : i = 0
    · subst i
      simp only [rowRhs,rowMatrix,if_true,x,mul_one]
      apply sum_nonneg
      intro p hp
      exact path_cost_nonneg I p (hS.1 p p.property).1.2.2.1 hc
    · simp only [rowRhs,rowMatrix,if_neg hi,x,mul_one]
      have he := hS.2 i hi
      rw [← Finset.sum_attach S] at he
      exact he.ge
  have hf := columnPoint_feasible I S x (fun _ => by positivity) hA
  refine ⟨columnPoint I S x, ⟨fun p hp => route_is_path3 I p (hS.1 p (hf.1 p hp)),hf.2⟩,?_⟩
  rw [columnPoint_objective]
  simp only [x,mul_one,solCost]
  exact Finset.sum_attach S (fun p => cost I p)

theorem lp_bounds_solutions (I : Instance n) (z : LPPoint n)
    (hz : LPOptimal I {p | IsPath3 I p} z)
    (hc : ∀ i j, I.arc i j → 0 ≤ I.c i j) :
    ∀ S, IsVRPTWSolution I S → objective I z ≤ solCost I S := by
  intro S hS
  obtain ⟨w,hw,he⟩ := solution_lp_point I hc S hS
  rw [← he]
  exact hz.2 w hw

end VRPTWProof


noncomputable section
namespace VRPTWProof
open VRPTWColGen92.Bound

theorem full_native_result {n : ℕ} (I : Instance n)
    (R₀ : Finset (List (Fin (n + 1)))) (hR₀ : ∀ p ∈ R₀, IsPath3 I p)
    (z : LPPoint n) (hz : LPOptimal I (↑R₀ : Set (List (Fin (n + 1)))) z)
    (y : DualPoint n) (hy : DualOptimal I R₀ y)
    (hprice : ∀ p, IsPath3 I p → 0 ≤ pathMarginal I y p) :
    LPOptimal I {p | IsPath3 I p} z ∧
    ((∀ i j, I.arc i j → 0 ≤ I.c i j) →
      (∀ S, IsVRPTWSolution I S → objective I z ≤ solCost I S) ∧
      ((∀ p, ∃ m : ℕ, z.x p = m) →
        (∀ i : Fin (n + 1), i ≠ 0 → ∑ p ∈ z.x.support, (p.count i : ℝ) * z.x p = 1) →
        IsVRPTWSolution I z.x.support ∧ solCost I z.x.support = objective I z ∧
          ∀ S, IsVRPTWSolution I S → solCost I z.x.support ≤ solCost I S)) := by
  have hfull := full_lp_optimal I R₀ hR₀ z hz y hy hprice
  refine ⟨hfull, fun hc => ⟨lp_bounds_solutions I z hfull hc, ?_⟩⟩
  intro hint hex
  obtain ⟨hsol,he⟩ := integral_support_solution I z hfull.1 hint hex
  refine ⟨hsol,he,?_⟩
  intro S hS
  rw [he]
  exact lp_bounds_solutions I z hfull hc S hS

end VRPTWProof


open VRPTWColGen92.Bound

namespace VRPTWColGen92.Bound
theorem colgen_certificate {n : ℕ} (I : Instance n)
    (R₀ : Finset (List (Fin (n + 1)))) (hR₀ : ∀ p ∈ R₀, IsPath3 I p)
    (z : LPPoint n) (hz : LPOptimal I (↑R₀ : Set (List (Fin (n + 1)))) z)
    (y : DualPoint n) (hy : DualOptimal I R₀ y)
    (hprice : ∀ p, IsPath3 I p → 0 ≤ pathMarginal I y p) :
    LPOptimal I {p | IsPath3 I p} z ∧
    ((∀ i j, I.arc i j → 0 ≤ I.c i j) →
      (∀ S, IsVRPTWSolution I S → objective I z ≤ solCost I S) ∧
      ((∀ p, ∃ m : ℕ, z.x p = m) →
        (∀ i : Fin (n + 1), i ≠ 0 → ∑ p ∈ z.x.support, (p.count i : ℝ) * z.x p = 1) →
        IsVRPTWSolution I z.x.support ∧ solCost I z.x.support = objective I z ∧
          ∀ S, IsVRPTWSolution I S → solCost I z.x.support ≤ solCost I S)) := by
  exact VRPTWProof.full_native_result I R₀ hR₀ z hz y hy hprice
end VRPTWColGen92.Bound

open VRPTWColGen92.Bound

theorem solution {n : ℕ} (I : Instance n)
    (R₀ : Finset (List (Fin (n + 1)))) (hR₀ : ∀ p ∈ R₀, IsPath3 I p)
    (z : LPPoint n) (hz : LPOptimal I (↑R₀ : Set (List (Fin (n + 1)))) z)
    (y : DualPoint n) (hy : DualOptimal I R₀ y)
    (hprice : ∀ p, IsPath3 I p → 0 ≤ pathMarginal I y p) :
    LPOptimal I {p | IsPath3 I p} z ∧
    ((∀ i j, I.arc i j → 0 ≤ I.c i j) →
      (∀ S, IsVRPTWSolution I S → objective I z ≤ solCost I S) ∧
      ((∀ p, ∃ m : ℕ, z.x p = m) →
        (∀ i : Fin (n + 1), i ≠ 0 → ∑ p ∈ z.x.support, (p.count i : ℝ) * z.x p = 1) →
        IsVRPTWSolution I z.x.support ∧ solCost I z.x.support = objective I z ∧
          ∀ S, IsVRPTWSolution I S → solCost I z.x.support ≤ solCost I S)) := VRPTWColGen92.Bound.colgen_certificate I R₀ hR₀ z hz y hy hprice
