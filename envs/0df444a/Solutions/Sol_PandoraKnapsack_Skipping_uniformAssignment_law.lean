-- Prove2me | solution 1 for PandoraKnapsack.Skipping.uniformAssignment_law
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T17:31:57.250793+00:00
-- url     : https://prove2.me/submissions/23ac638e-be47-46bb-9e9d-828ea09d751c

import Definitions.Def_PandoraKnapsack_Skipping_UniformAssignment
import Definitions.Def_PandoraKnapsack_Skipping_Machine

open MeasureTheory Set
open PandoraKnapsack.Skipping
namespace PandoraKnapsack.Skipping
variable {d n m T B : ℕ}

private lemma cell_next (p : Fin d → ℝ) (k : Fin d) :
    cellStart p (k.val+1) = cellStart p k.val + p k := by
  have h : (Finset.univ.filter (fun z : Fin d => z.val < k.val+1)) =
      insert k (Finset.univ.filter (fun z : Fin d => z.val < k.val)) := by
    ext z; simp [Fin.ext_iff]; omega
  unfold cellStart
  rw [h,Finset.sum_insert (by simp)]
  ac_rfl

private lemma cell_mono (p : Fin d → ℝ) (hp : ∀ k, 0 ≤ p k) : Monotone (cellStart p) := by
  intro a b hab
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hk).2.trans_le hab⟩
  · exact fun i _ _ => hp i

private lemma cell_total (p : Fin d → ℝ) : cellStart p d = ∑ k, p k := by
  simp [cellStart]

private lemma cell_some (p : Fin d → ℝ) (hp : ∀ k, 0 ≤ p k) (u : ℝ) (k : Fin d) :
    uniformCell p u = some k ↔ cellStart p k.val ≤ u ∧ u < cellStart p k.val + p k := by
  change k ∈ Fin.find? _ ↔ _
  rw [Fin.mem_find?_iff]
  simp only [decide_eq_true_eq]
  refine ⟨And.left, fun h => ⟨h,?_⟩⟩
  intro j hj h'
  have hprefix : cellStart p (j.val+1) ≤ cellStart p k.val := cell_mono p hp (by exact hj)
  rw [cell_next] at hprefix
  linarith [h.1,h'.2]

private lemma cell_none (p : Fin d → ℝ) (hp : ∀ k, 0 ≤ p k) (u : ℝ) (hu : 0 ≤ u) :
    uniformCell p u = none ↔ ∑ k, p k ≤ u := by
  have covers (s : ℕ) (hs : s ≤ d) (hu' : u < cellStart p s) :
      ∃ k, uniformCell p u = some k := by
    induction s with
    | zero => simp [cellStart] at hu'; linarith
    | succ s ih =>
      by_cases h : u < cellStart p s
      · exact ih (by omega) h
      · let k : Fin d := ⟨s,by omega⟩
        refine ⟨k,(cell_some p hp u k).mpr ⟨le_of_not_gt h,?_⟩⟩
        rw [← cell_next]; exact hu'
  constructor
  · intro hn
    by_contra! h
    obtain ⟨k,hk⟩ := covers d le_rfl (by rwa [cell_total])
    simp [hn] at hk
  · intro h
    cases hc : uniformCell p u with
    | none => rfl
    | some k =>
      have hu' := ((cell_some p hp u k).mp hc).2
      have hle := cell_mono p hp (show k.val+1 ≤ d from k.isLt)
      rw [cell_next,cell_total] at hle
      linarith

private abbrev Labels (m T : ℕ) := Fin m × Fin (T+1)
private noncomputable def rowMass (x : LPArray n m) (lab : Fin d → Labels m T) (i : Fin n) (k : Fin d) : ℝ :=
  x i (lab k).1 (lab k).2.val / 4

private lemma row_total (x : LPArray n m) (lab : Fin d → Labels m T) (hi : Function.Injective lab)
    (hs : ∀ (i : Fin n) (j : Fin m) (t : Fin (T+1)), x i j t.val ≠ 0 → ∃ k, lab k = (j,t))
    (i : Fin n) :
    (∑ k, rowMass x lab i k) = (∑ j, ∑ t ∈ Finset.range (T+1), x i j t) / 4 := by
  let f (v : Labels m T) := x i v.1 v.2.val / 4
  calc
    _ = ∑ v, f v := by
      apply Fintype.sum_of_injective lab hi
      · rintro ⟨j,t⟩ h
        have h0 : x i j t.val = 0 := by
          by_contra hn; exact h (hs i j t hn)
        simp [f,h0]
      · intro k; rfl
    _ = _ := by
      simp only [Fintype.sum_prod_type, f, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      exact Fin.sum_univ_eq_sum_range (fun u => x i j u / 4) (T+1)

private noncomputable def rowFiber (p : Fin d → ℝ) (lab : Fin d → Labels m T)
    (o : Option (Labels m T)) : Set unitInterval :=
  {u | (uniformCell p (u:ℝ)).map lab = o}

private lemma fiber_none (p : Fin d → ℝ) (hp : ∀ k, 0 ≤ p k) (h1 : ∑ k, p k ≤ 1)
    (lab : Fin d → Labels m T) :
    rowFiber p lab none = Ici (⟨∑ k, p k, Finset.sum_nonneg (fun k _ => hp k),h1⟩ : unitInterval) := by
  ext u
  simp [rowFiber,cell_none p hp _ u.2.1]; rfl

private lemma fiber_some (p : Fin d → ℝ) (hp : ∀ k, 0 ≤ p k) (h1 : ∑ k, p k ≤ 1)
    (lab : Fin d → Labels m T) (hinj : Function.Injective lab) (k : Fin d) :
    ∃ L R : unitInterval, rowFiber p lab (some (lab k)) = Ico L R ∧ (R:ℝ) - L = p k := by
  have h0 : 0 ≤ cellStart p k.val := Finset.sum_nonneg fun z _ => hp z
  have hr : cellStart p k.val + p k ≤ 1 := by
    rw [← cell_next]
    exact (cell_mono p hp k.isLt).trans ((cell_total p) ▸ h1)
  let L : unitInterval := ⟨cellStart p k.val,h0,by linarith [hp k]⟩
  let R : unitInterval := ⟨cellStart p k.val+p k,add_nonneg h0 (hp k),hr⟩
  refine ⟨L,R,?_, by dsimp [L,R]; ring⟩
  ext u
  change ((uniformCell p (u:ℝ)).map lab = some (lab k)) ↔ _
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨v,hv,he⟩
    obtain rfl := hinj he
    exact (cell_some p hp _ _).mp hv
  · intro hu; exact ⟨k,(cell_some p hp _ k).mpr hu,rfl⟩

private lemma row_law (I : Instance n m T) (x : LPArray n m) (hx : PsiFeasible I T x)
    (lab : Fin d → Labels m T) (hi : Function.Injective lab)
    (hs : ∀ (i : Fin n) (j : Fin m) (t : Fin (T+1)), x i j t.val ≠ 0 → ∃ k, lab k = (j,t))
    (i : Fin n) (o : Option (Labels m T)) :
    MeasurableSet (rowFiber (rowMass x lab i) lab o) ∧
    volume.real (rowFiber (rowMass x lab i) lab o) = assignWeight x i o := by
  let p := rowMass x lab i
  have hp (k : Fin d) : 0 ≤ p k :=
    div_nonneg (hx.2.2 i (lab k).1 (lab k).2.val (by omega)).1 (by norm_num)
  have ht : ∑ k, p k = (∑ j, ∑ t ∈ Finset.range (T+1), x i j t)/4 := row_total x lab hi hs i
  have h1 : ∑ k, p k ≤ 1 := by linarith [hx.2.1 i]
  change MeasurableSet (rowFiber p lab o) ∧ volume.real (rowFiber p lab o) = _
  rcases o with _ | ⟨j,t⟩
  · rw [fiber_none p hp h1]
    refine ⟨measurableSet_Ici,?_⟩
    rw [Measure.real, unitInterval.volume_Ici, ENNReal.toReal_ofReal]
    · change 1 - ∑ k, p k = _
      rw [ht]; rfl
    · exact sub_nonneg.mpr h1
  · by_cases hm : ∃ k, lab k = (j,t)
    · obtain ⟨k,hk⟩ := hm
      obtain ⟨L,R,hf,hval⟩ := fiber_some p hp h1 lab hi k
      rw [hk] at hf
      rw [hf]
      refine ⟨measurableSet_Ico,?_⟩
      simp only [Measure.real,unitInterval.volume_Ico,hval,ENNReal.toReal_ofReal (hp k)]
      simp [p,rowMass,hk,assignWeight]
    · have hz : x i j t = 0 := by by_contra hn; exact hm (hs i j t hn)
      have hf : rowFiber p lab (some (j,t)) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro u hu
        obtain ⟨k,_,hk⟩ := Option.map_eq_some_iff.mp hu
        exact hm ⟨k,hk⟩
      simp [hf,assignWeight,hz]

private lemma assignment_fiber (I : Instance n m T) (x : LPArray n m) (hx : PsiFeasible I T x)
    (hB : n ≤ B) (lab : Fin d → Labels m T) (hi : Function.Injective lab)
    (hs : ∀ (i : Fin n) (j : Fin m) (t : Fin (T+1)), x i j t.val ≠ 0 → ∃ k, lab k = (j,t))
    (a : Assignment n m T) :
    MeasurableSet {ω | uniformAssignment hB lab x ω = a} ∧
    (drawLaw B).real {ω | uniformAssignment hB lab x ω = a} = ∏ i, assignWeight x i (a i) := by
  let R (v : Fin B) : Set unitInterval :=
    if h : v.val < n then rowFiber (rowMass x lab ⟨v.val,h⟩) lab (a ⟨v.val,h⟩) else univ
  have hR (i : Fin n) :
      R (i.castLE hB) = rowFiber (rowMass x lab i) lab (a i) := by simp [R,i.isLt]
  have hset : {ω | uniformAssignment hB lab x ω = a} = univ.pi R := by
    ext ω
    constructor
    · intro h v _
      by_cases hv : v.val < n
      · have hh := congrFun h (⟨v.val,hv⟩ : Fin n)
        rw [show R v = rowFiber (rowMass x lab ⟨v.val,hv⟩) lab (a ⟨v.val,hv⟩) by exact hR ⟨v.val,hv⟩]
        exact hh
      · simp [R,hv]
    · intro h
      funext i
      have hi' := h (i.castLE hB) (Set.mem_univ _)
      rw [hR] at hi'
      exact hi'
  rw [hset]
  constructor
  · apply MeasurableSet.univ_pi
    intro v
    by_cases hv : v.val < n
    · simpa [R,hv] using (row_law I x hx lab hi hs ⟨v.val,hv⟩ (a ⟨v.val,hv⟩)).1
    · simp [R,hv]
  · rw [Measure.real,drawLaw,Measure.pi_pi, ENNReal.toReal_prod]
    symm
    apply Fintype.prod_of_injective (fun i : Fin n => i.castLE hB) (by intro i j h; exact Fin.ext (congrArg (@Fin.val B) h))
    · intro v hv
      have hv' : ¬ v.val < n := fun h => hv ⟨⟨v.val,h⟩,rfl⟩
      simp [R,hv']
    · intro i
      rw [hR]
      exact (row_law I x hx lab hi hs i (a i)).2.symm

end PandoraKnapsack.Skipping

theorem solution {n m T d B : ℕ} (I : Instance n m T) (x : LPArray n m) (hx : PsiFeasible I T x)
    (hB : n ≤ B) (lab : Fin d → Fin m × Fin (T+1)) (hinj : Function.Injective lab)
    (hsupp : ∀ (i : Fin n) (j : Fin m) (t : Fin (T+1)), x i j t.val ≠ 0 → ∃ k, lab k = (j,t)) :
    Integrable (fun ω => skipValue I (alg1Policy (uniformAssignment hB lab x ω))) (drawLaw B) ∧
    (∫ ω, skipValue I (alg1Policy (uniformAssignment hB lab x ω)) ∂drawLaw B) = alg1Utility I x := by
  classical
  let A := uniformAssignment hB lab x
  let v (a : Assignment n m T) := skipValue I (alg1Policy a)
  let f (a : Assignment n m T) := ({ω | A ω = a} : Set _).indicator (fun _ => v a)
  have hf (ω) : v (A ω) = ∑ a, f a ω := by
    simp [f,Set.indicator_apply,Finset.sum_ite_eq]
  have hmeas (a : Assignment n m T) : MeasurableSet {ω | A ω = a} :=
    (assignment_fiber I x hx hB lab hinj hsupp a).1
  have hprob : IsProbabilityMeasure (drawLaw B) := by unfold drawLaw; infer_instance
  have hint (a) : Integrable (f a) (drawLaw B) := (integrable_const _).indicator (hmeas a)
  change Integrable (fun ω => v (A ω)) _ ∧ (∫ ω, v (A ω) ∂drawLaw B) = _
  simp_rw [hf]
  refine ⟨integrable_finsetSum _ (fun i _ => hint i),?_⟩
  rw [integral_finsetSum _ (fun i _ => hint i)]
  apply Finset.sum_congr rfl
  intro a _
  rw [show (∫ ω, f a ω ∂drawLaw B) = (drawLaw B).real {ω | A ω = a} • v a from
    integral_indicator_const _ (hmeas a)]
  rw [(assignment_fiber I x hx hB lab hinj hsupp a).2]
  rfl
