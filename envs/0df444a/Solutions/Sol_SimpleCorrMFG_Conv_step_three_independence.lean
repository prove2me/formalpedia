-- Prove2me | solution 1 for SimpleCorrMFG.Conv.step_three_independence
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T06:21:49.639287+00:00
-- url     : https://prove2.me/submissions/cddca4a0-ab62-4e6e-ae34-cfd8d2da5713

import Mathlib
import Definitions.Def_SimpleCorrMFG_Conv_Model
import Definitions.Def_SimpleCorrMFG_Conv_NPlayer
import Definitions.Def_SimpleCorrMFG_Conv_Coupling

open MeasureTheory ProbabilityTheory unitInterval Filter Topology SimpleCorrMFG.Conv

lemma measurable_iterFin_go {Ω C : Type} [MeasurableSpace Ω] [MeasurableSpace C] [Countable C]
    [MeasurableSingletonClass C] {T : ℕ} (s₀ : Ω → C) (hs₀ : Measurable s₀)
    (step : Ω → Fin T → C → C) (hstep : ∀ t c, Measurable (fun ω => step ω t c)) :
    ∀ k : ℕ, Measurable (fun ω => iterFin.go (s₀ ω) (step ω) k) := by
  intro k
  induction k with
  | zero => simpa [iterFin.go] using hs₀
  | succ k ih =>
    by_cases hk : k < T
    · simp only [iterFin.go, dif_pos hk]
      have : Measurable (fun p : Ω × C => step p.1 ⟨k, hk⟩ p.2) :=
        measurable_from_prod_countable_left (fun c => hstep _ c)
      exact this.comp (measurable_id.prodMk ih)
    · simpa [iterFin.go, dif_neg hk] using ih

lemma measurable_iterFin {Ω C : Type} [MeasurableSpace Ω] [MeasurableSpace C] [Countable C]
    [MeasurableSingletonClass C] {T : ℕ} (s₀ : Ω → C) (hs₀ : Measurable s₀)
    (step : Ω → Fin T → C → C) (hstep : ∀ t c, Measurable (fun ω => step ω t c)) (t : Fin (T + 1)) :
    Measurable (fun ω => iterFin (s₀ ω) (step ω) t) :=
  measurable_iterFin_go s₀ hs₀ step hstep t.val

section
variable {T : ℕ} {X Γ : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    [MeasurableSpace X] [DiscreteMeasurableSpace X]
    [Fintype Γ] [MeasurableSpace Γ] [DiscreteMeasurableSpace Γ]

lemma measurable_Ψ_app (M : Model T X Γ) (hM : M.Standing) {Ω : Type} [MeasurableSpace Ω]
    (t : Fin T) (x : X) (m : Meas X) (a : Ω → Γ) (ha : Measurable a) (z : Ω → I) (hz : Measurable z) :
    Measurable (fun ω => M.Ψ t x m (a ω) (z ω)) :=
  (hM.1 t).comp (measurable_const.prodMk (measurable_const.prodMk (ha.prodMk hz)))

lemma measurable_hatPath (M : Model T X Γ) (hM : M.Standing) {N : ℕ} [NeZero N] (t : Fin (T + 1)) :
    Measurable (fun ω : NOmega T N X Γ => hatPath M ω t) := by
  unfold hatPath
  refine measurable_iterFin (fun ω : NOmega T N X Γ => ω.1) measurable_fst
    (fun ω t x j => M.Ψ t (x j) (empOthers x 0) (ω.2.1 j t (x j)) (ω.2.2 t j)) (fun s x => ?_) t
  refine measurable_pi_lambda _ (fun j => ?_)
  refine measurable_Ψ_app M hM s _ _ _ ?_ _ ?_
  · fun_prop
  · fun_prop

lemma measurable_nPath (M : Model T X Γ) (hM : M.Standing) {N : ℕ} (i : Fin N)
    (u : Strat T X Γ → Strat T X Γ) (t : Fin (T + 1)) :
    Measurable (fun ω : NOmega T N X Γ => nPath M i u ω t) := by
  unfold nPath
  refine measurable_iterFin (fun ω : NOmega T N X Γ => ω.1) measurable_fst
    (fun ω t x j => M.Ψ t (x j) (empOthers x j) (played i u ω.2.1 j t (x j)) (ω.2.2 t j)) (fun s x => ?_) t
  refine measurable_pi_lambda _ (fun j => ?_)
  refine measurable_Ψ_app M hM s _ _ _ ?_ _ ?_
  · unfold played
    by_cases h : j = i
    · simp only [h, if_true]
      have : Measurable (fun φ : Strat T X Γ => u φ s (x i)) := measurable_of_countable _
      exact this.comp (by fun_prop)
    · simp only [h, if_false]; fun_prop
  · fun_prop


section generic
variable {Ω Ω' α β δ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace α]
  [MeasurableSpace β] [MeasurableSpace δ]

lemma indepFun_comp_measurePreserving {μ : Measure Ω} {μ' : Measure Ω'} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure μ'] {f : Ω → α} {g : Ω → β} (hf : Measurable f) (hg : Measurable g)
    (h : IndepFun f g μ) {T : Ω' → Ω} (hT : MeasurePreserving T μ' μ) :
    IndepFun (f ∘ T) (g ∘ T) μ' := by
  rw [indepFun_iff_map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable] at h
  rw [indepFun_iff_map_prod_eq_prod_map_map (hf.comp hT.measurable).aemeasurable
    (hg.comp hT.measurable).aemeasurable]
  have e1 : μ'.map (fun ω => ((f ∘ T) ω, (g ∘ T) ω)) = μ.map (fun ω => (f ω, g ω)) := by
    rw [← hT.map_eq, Measure.map_map (hf.prodMk hg) hT.measurable]; rfl
  rw [e1, h, ← Measure.map_map hf hT.measurable, ← Measure.map_map hg hT.measurable, hT.map_eq]

/-- Independence on the left factor of a product extends to the product. -/
lemma indepFun_prod_left {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {f : Ω → α} {g : Ω → β} (hf : Measurable f) (hg : Measurable g)
    (h : IndepFun f g μ) :
    IndepFun (fun ω : Ω × Ω' => f ω.1) (fun ω => (g ω.1, ω.2)) (μ.prod ν) := by
  rw [indepFun_iff_map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable] at h
  have hf1 : Measurable (fun ω : Ω × Ω' => f ω.1) := hf.comp measurable_fst
  have hg1 : Measurable (fun ω : Ω × Ω' => (g ω.1, ω.2)) := (hg.comp measurable_fst).prodMk measurable_snd
  rw [indepFun_iff_map_prod_eq_prod_map_map hf1.aemeasurable hg1.aemeasurable]
  have eA : (μ.prod ν).map (fun ω : Ω × Ω' => f ω.1) = μ.map f := by
    rw [show (fun ω : Ω × Ω' => f ω.1) = f ∘ Prod.fst from rfl,
      ← Measure.map_map hf measurable_fst, Measure.map_fst_prod, measure_univ, one_smul]
  have eB : (μ.prod ν).map (fun ω : Ω × Ω' => (g ω.1, ω.2)) = (μ.map g).prod ν := by
    have hp := Measure.map_prod_map μ ν hg measurable_id
    rw [Measure.map_id] at hp
    rw [hp]; rfl
  have eAB : (μ.prod ν).map (fun ω : Ω × Ω' => (f ω.1, (g ω.1, ω.2))) =
      ((μ.map f).prod ((μ.map g).prod ν)) := by
    have : (fun ω : Ω × Ω' => (f ω.1, (g ω.1, ω.2))) =
        (MeasurableEquiv.prodAssoc : (α × β) × Ω' ≃ᵐ α × (β × Ω')) ∘
          (Prod.map (fun ω => (f ω, g ω)) id) := rfl
    rw [this, ← Measure.map_map (MeasurableEquiv.prodAssoc).measurable
      ((hf.prodMk hg).prodMap measurable_id)]
    have hp := Measure.map_prod_map μ ν (hf.prodMk hg) measurable_id
    rw [Measure.map_id, h] at hp
    rw [← hp]
    exact (measurePreserving_prodAssoc (μ.map f) (μ.map g) ν).map_eq
  rw [eAB, eA, eB]

/-- Independence on the right factor of a product extends to the product. -/
lemma indepFun_prod_right {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {f : Ω' → α} {g : Ω' → β} (hf : Measurable f) (hg : Measurable g)
    (h : IndepFun f g ν) :
    IndepFun (fun ω : Ω × Ω' => f ω.2) (fun ω => (ω.1, g ω.2)) (μ.prod ν) := by
  have h1 := indepFun_prod_left (ν := μ) hf hg h
  have h2 := indepFun_comp_measurePreserving (hf.comp measurable_fst)
    ((hg.comp measurable_fst).prodMk measurable_snd) h1 (Measure.measurePreserving_swap (μ := μ) (ν := ν))
  have h3 := h2.comp measurable_id (measurable_swap)
  exact h3

/-- Coordinatewise independence over a finite product. -/
lemma indepFun_pi_of_forall {ι : Type*} [Fintype ι] {Ωi : Type*} [MeasurableSpace Ωi]
    (μ : ι → Measure Ωi) [∀ i, IsProbabilityMeasure (μ i)] {f : ι → Ωi → α} {g : ι → Ωi → β}
    (hf : ∀ i, Measurable (f i)) (hg : ∀ i, Measurable (g i)) (h : ∀ i, IndepFun (f i) (g i) (μ i)) :
    IndepFun (fun ω i => f i (ω i)) (fun ω i => g i (ω i)) (Measure.pi μ) := by
  have hF : Measurable (fun (ω : ι → Ωi) i => f i (ω i)) :=
    measurable_pi_lambda _ (fun i => (hf i).comp (measurable_pi_apply i))
  have hG : Measurable (fun (ω : ι → Ωi) i => g i (ω i)) :=
    measurable_pi_lambda _ (fun i => (hg i).comp (measurable_pi_apply i))
  rw [indepFun_iff_map_prod_eq_prod_map_map hF.aemeasurable hG.aemeasurable]
  have hpair : ∀ i, (μ i).map (fun ω => (f i ω, g i ω)) = ((μ i).map (f i)).prod ((μ i).map (g i)) :=
    fun i => (indepFun_iff_map_prod_eq_prod_map_map (hf i).aemeasurable (hg i).aemeasurable).1 (h i)
  have eF : (Measure.pi μ).map (fun ω i => f i (ω i)) = Measure.pi (fun i => (μ i).map (f i)) :=
    Measure.pi_map_pi (fun i => (hf i).aemeasurable)
  have eG : (Measure.pi μ).map (fun ω i => g i (ω i)) = Measure.pi (fun i => (μ i).map (g i)) :=
    Measure.pi_map_pi (fun i => (hg i).aemeasurable)
  have ePair : (Measure.pi μ).map (fun ω i => (f i (ω i), g i (ω i))) =
      Measure.pi (fun i => ((μ i).map (f i)).prod ((μ i).map (g i))) := by
    rw [Measure.pi_map_pi (fun i => ((hf i).prodMk (hg i)).aemeasurable)]
    simp_rw [hpair]
  have : (fun ω : ι → Ωi => ((fun i => f i (ω i)), (fun i => g i (ω i)))) =
      (MeasurableEquiv.arrowProdEquivProdArrow α β ι) ∘ (fun ω i => (f i (ω i), g i (ω i))) := rfl
  have hm : Measurable (fun (ω : ι → Ωi) i => (f i (ω i), g i (ω i))) :=
    measurable_pi_lambda _ (fun i => ((hf i).prodMk (hg i)).comp (measurable_pi_apply i))
  rw [this, ← Measure.map_map (MeasurableEquiv.arrowProdEquivProdArrow α β ι).measurable hm, ePair,
    (measurePreserving_arrowProdEquivProdArrow α β ι _ _).map_eq, eF, eG]

/-- Under an i.i.d. product over `Fin N`, coordinate `0` is independent of the others. -/
lemma indepFun_pi_zero_rest {N : ℕ} [NeZero N] (ρ : Measure α) [IsProbabilityMeasure ρ] :
    IndepFun (fun x : Fin N → α => x 0)
      (fun x (i : ↥(Finset.univ.erase (0 : Fin N))) => x i) (Measure.pi fun _ => ρ) := by
  have hi : iIndepFun (fun (i : Fin N) (x : Fin N → α) => x i) (Measure.pi fun _ => ρ) :=
    iIndepFun_pi (X := fun _ (a : α) => a) (fun _ => measurable_id.aemeasurable)
  have h := hi.indepFun_finset {0} (Finset.univ.erase 0) (by simp) (fun i => measurable_pi_apply i)
  have h2 : IndepFun ((fun y : ↥({0} : Finset (Fin N)) → α => y ⟨0, by simp⟩) ∘
      (fun (a : Fin N → α) (i : ↥({0} : Finset (Fin N))) => a i))
      (id ∘ (fun (a : Fin N → α) (i : ↥(Finset.univ.erase (0 : Fin N))) => a i))
      (Measure.pi fun _ => ρ) :=
    h.comp (measurable_pi_apply _) measurable_id
  exact h2
end generic

section specific
variable {T : ℕ} {X Γ : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    [MeasurableSpace X] [DiscreteMeasurableSpace X]
    [Fintype Γ] [MeasurableSpace Γ] [DiscreteMeasurableSpace Γ]

lemma empOn_congr' {ι : Type} (S : Finset ι) (x x' : ι → X) (h : ∀ j ∈ S, x j = x' j) :
    empOn S x = empOn S x' := by
  unfold empOn
  split_ifs with hS
  · apply Subtype.ext; funext y
    show (∑ j ∈ S, if x j = y then (1:ℝ) else 0) / (S.card : ℝ) =
      (∑ j ∈ S, if x' j = y then (1:ℝ) else 0) / (S.card : ℝ)
    rw [Finset.sum_congr rfl (fun j hj => by rw [h j hj])]
  · rfl

lemma hatPath_congr (M : Model T X Γ) {N : ℕ} [NeZero N] (ω ω' : NOmega T N X Γ)
    (h1 : ∀ j, j ≠ 0 → ω.1 j = ω'.1 j) (h2 : ω.2.1 = ω'.2.1)
    (h3 : ∀ t j, j ≠ 0 → ω.2.2 t j = ω'.2.2 t j) (t : Fin (T + 1)) :
    ∀ j, j ≠ 0 → hatPath M ω t j = hatPath M ω' t j := by
  unfold hatPath iterFin
  generalize t.val = k
  induction k with
  | zero => exact h1
  | succ k ih =>
    intro j hj
    by_cases hk : k < T
    · simp only [iterFin.go, dif_pos hk]
      have he : empOthers (iterFin.go ω.1 (fun t x j => M.Ψ t (x j) (empOthers x 0)
            (ω.2.1 j t (x j)) (ω.2.2 t j)) k) 0 =
          empOthers (iterFin.go ω'.1 (fun t x j => M.Ψ t (x j) (empOthers x 0)
            (ω'.2.1 j t (x j)) (ω'.2.2 t j)) k) 0 :=
        empOn_congr' _ _ _ (fun l hl => ih l (Finset.mem_erase.mp hl).1)
      rw [he, ih j hj, h2, h3 _ j hj]
    · simp only [iterFin.go, dif_neg hk]
      exact ih j hj

lemma hatEmp_congr (M : Model T X Γ) {N : ℕ} [NeZero N] (ω ω' : NOmega T N X Γ)
    (h1 : ∀ j, j ≠ 0 → ω.1 j = ω'.1 j) (h2 : ω.2.1 = ω'.2.1)
    (h3 : ∀ t j, j ≠ 0 → ω.2.2 t j = ω'.2.2 t j) (t : Fin (T + 1)) :
    hatEmp M ω t = hatEmp M ω' t :=
  empOn_congr' _ _ _ (fun l hl => hatPath_congr M ω ω' h1 h2 h3 t l (Finset.mem_erase.mp hl).1)

lemma measurable_hatEmp (M : Model T X Γ) (hM : M.Standing) {N : ℕ} [NeZero N] (t : Fin (T + 1)) :
    Measurable (fun ω : NOmega T N X Γ => hatEmp M ω t) :=
  (measurable_of_countable (fun x : Fin N → X => empOthers x 0)).comp (measurable_hatPath M hM t)

/-- Extend a vector indexed by the players `≠ 0` by the value `c` at player `0`. -/
def extZero {α : Type} {N : ℕ} [NeZero N] (c : α) (xr : ↥(Finset.univ.erase (0 : Fin N)) → α) :
    Fin N → α :=
  fun j => if h : j = 0 then c else xr ⟨j, by simp [h]⟩

lemma measurable_extZero {α : Type} [MeasurableSpace α] {N : ℕ} [NeZero N] (c : α) :
    Measurable (extZero (N := N) c) := by
  refine measurable_pi_lambda _ (fun j => ?_)
  unfold extZero
  by_cases h : j = 0
  · simp only [h, dif_pos]; exact measurable_const
  · simp only [h, dif_neg, not_false_eq_true]; exact measurable_pi_apply _

lemma extZero_ne {α : Type} {N : ℕ} [NeZero N] (c : α) (x : Fin N → α) (j : Fin N) (hj : j ≠ 0) :
    extZero c (fun i : ↥(Finset.univ.erase (0 : Fin N)) => x i) j = x j := by
  simp [extZero, hj]

end specific

theorem solution {T : ℕ} {X Γ : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    [TopologicalSpace X] [DiscreteTopology X] [MeasurableSpace X] [DiscreteMeasurableSpace X]
    [Fintype Γ] [Nonempty Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] [MeasurableSpace Γ]
    [DiscreteMeasurableSpace Γ]
    (M : Model T X Γ) (hM : M.Standing) {N : ℕ} [NeZero N] (hN : 2 ≤ N) (m : Meas X)
    (γ : ProbabilityMeasure (Fin N → Strat T X Γ)) :
    IndepFun (fun ω : NOmega T N X Γ => ω.1 0)
        (fun ω => ((fun t => ω.2.2 t 0), (ω.2.1 0, fun t => hatEmp M ω t)))
        (nLaw (prodInit N m) γ) ∧
      IndepFun (fun ω : NOmega T N X Γ => fun t => ω.2.2 t 0)
        (fun ω => (ω.2.1 0, fun t => hatEmp M ω t)) (nLaw (prodInit N m) γ) := by
  set S0 := (Finset.univ.erase (0 : Fin N))
  have hP : nLaw (prodInit N m) γ =
      (Measure.pi fun _ : Fin N => ((m.toPM : ProbabilityMeasure X) : Measure X)).prod
        ((γ : Measure (Fin N → Strat T X Γ)).prod
          (Measure.pi fun _ : Fin T => Measure.pi fun _ : Fin N => (volume : Measure I))) := rfl
  rw [hP]
  constructor
  · have hI1 := indepFun_pi_zero_rest (N := N) ((m.toPM : ProbabilityMeasure X) : Measure X)
    have hA := indepFun_prod_left (ν := (γ : Measure (Fin N → Strat T X Γ)).prod
          (Measure.pi fun _ : Fin T => Measure.pi fun _ : Fin N => (volume : Measure I)))
      (measurable_pi_apply 0) (measurable_pi_lambda _ (fun i => measurable_pi_apply _)) hI1
    set K : (↥S0 → X) × ((Fin N → Strat T X Γ) × (Fin T → Fin N → I)) →
        (Fin T → I) × (Strat T X Γ × (Fin (T + 1) → Meas X)) :=
      fun p => ((fun t => p.2.2 t 0), (p.2.1 0, fun t => hatEmp M (extZero (Classical.arbitrary X) p.1, p.2) t))
      with hKdef
    have hK : Measurable K := by
      refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)
      · exact measurable_pi_lambda _ (fun t => (measurable_pi_apply 0).comp
          ((measurable_pi_apply t).comp (measurable_snd.comp measurable_snd)))
      · exact (measurable_pi_apply 0).comp (measurable_fst.comp measurable_snd)
      · exact measurable_pi_lambda _ (fun t => (measurable_hatEmp M hM t).comp
          (((measurable_extZero _).comp measurable_fst).prodMk measurable_snd))
    have h := hA.comp measurable_id hK
    refine h.congr (ae_of_all _ (fun ω => rfl)) (ae_of_all _ (fun ω => ?_))
    simp only [Function.comp_apply, hKdef]
    congr 2
    funext t
    exact hatEmp_congr M (extZero (Classical.arbitrary X) (fun i : ↥S0 => ω.1 i), ω.2) ω
      (fun j hj => extZero_ne _ ω.1 j hj) rfl (fun _ _ _ => rfl) t
  · have hI2 := indepFun_pi_of_forall (fun _ : Fin T => Measure.pi fun _ : Fin N => (volume : Measure I))
      (f := fun _ (v : Fin N → I) => v 0) (g := fun _ (v : Fin N → I) (i : ↥S0) => v i)
      (fun _ => measurable_pi_apply 0) (fun _ => measurable_pi_lambda _ (fun i => measurable_pi_apply _))
      (fun _ => indepFun_pi_zero_rest (N := N) (volume : Measure I))
    have hB1 := indepFun_prod_right (μ := (γ : Measure (Fin N → Strat T X Γ)))
      (measurable_pi_lambda _ (fun t => (measurable_pi_apply 0).comp (measurable_pi_apply t)))
      (measurable_pi_lambda _ (fun t => measurable_pi_lambda _ (fun i =>
        (measurable_pi_apply _).comp (measurable_pi_apply t)))) hI2
    have hB2 := indepFun_prod_right
      (μ := Measure.pi fun _ : Fin N => ((m.toPM : ProbabilityMeasure X) : Measure X))
      ((measurable_pi_lambda _ (fun t => (measurable_pi_apply 0).comp (measurable_pi_apply t))).comp
        measurable_snd)
      (measurable_fst.prodMk ((measurable_pi_lambda _ (fun t => measurable_pi_lambda _ (fun i =>
        (measurable_pi_apply _).comp (measurable_pi_apply t)))).comp measurable_snd)) hB1
    set H : (Fin N → X) × ((Fin N → Strat T X Γ) × (Fin T → ↥S0 → I)) →
        Strat T X Γ × (Fin (T + 1) → Meas X) :=
      fun q => (q.2.1 0, fun t => hatEmp M (q.1, q.2.1, fun s => extZero (0 : I) (q.2.2 s)) t)
      with hHdef
    have hH : Measurable H := by
      refine Measurable.prodMk ?_ ?_
      · exact (measurable_pi_apply 0).comp (measurable_fst.comp measurable_snd)
      · refine measurable_pi_lambda _ (fun t => (measurable_hatEmp M hM t).comp ?_)
        refine measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk ?_)
        exact measurable_pi_lambda _ (fun s => (measurable_extZero _).comp
          ((measurable_pi_apply s).comp (measurable_snd.comp measurable_snd)))
    have h := hB2.comp measurable_id hH
    refine h.congr (ae_of_all _ (fun ω => rfl)) (ae_of_all _ (fun ω => ?_))
    simp only [Function.comp_apply, hHdef]
    congr 2
    funext t
    exact hatEmp_congr M (ω.1, ω.2.1, fun s => extZero (0 : I) (fun i : ↥S0 => ω.2.2 s i)) ω
      (fun _ _ => rfl) rfl (fun s j hj => extZero_ne _ (ω.2.2 s) j hj) t
