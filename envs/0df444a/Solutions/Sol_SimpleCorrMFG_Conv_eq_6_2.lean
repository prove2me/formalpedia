-- Prove2me | solution 1 for SimpleCorrMFG.Conv.eq_6_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T06:37:36.974612+00:00
-- url     : https://prove2.me/submissions/fbd7ec5b-fbdc-4437-8834-c6528cef0989

import Mathlib
import Definitions.Def_SimpleCorrMFG_Conv_Model
import Definitions.Def_SimpleCorrMFG_Conv_NPlayer
import Definitions.Def_SimpleCorrMFG_Conv_Coupling
import Theorems.Thm_SimpleCorrMFG_Conv_eq_6_3

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


section lib2

lemma indepFun_pi_at_rest {α : Type*} [MeasurableSpace α] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ι → Measure α) [∀ i, IsProbabilityMeasure (μ i)] (k : ι) :
    IndepFun (fun x : ι → α => x k) (fun x (i : ↥(Finset.univ.erase k)) => x i) (Measure.pi μ) := by
  have hi : iIndepFun (fun (i : ι) (x : ι → α) => x i) (Measure.pi μ) :=
    iIndepFun_pi (X := fun _ (a : α) => a) (fun _ => measurable_id.aemeasurable)
  have h := hi.indepFun_finset {k} (Finset.univ.erase k) (by simp) (fun i => measurable_pi_apply i)
  have h2 : IndepFun ((fun y : ↥({k} : Finset ι) → α => y ⟨k, by simp⟩) ∘
      (fun (a : ι → α) (i : ↥({k} : Finset ι)) => a i))
      (id ∘ (fun (a : ι → α) (i : ↥(Finset.univ.erase k)) => a i)) (Measure.pi μ) :=
    h.comp (measurable_pi_apply _) measurable_id
  exact h2

/-- Extend a vector indexed by `univ.erase k` by the value `c` at `k`. -/
def extAt {ι α : Type*} [Fintype ι] [DecidableEq ι] (k : ι) (c : α)
    (xr : ↥(Finset.univ.erase k) → α) : ι → α :=
  fun j => if h : j = k then c else xr ⟨j, by simp [h]⟩

lemma measurable_extAt {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α] (k : ι) (c : α) :
    Measurable (extAt k c) := by
  refine measurable_pi_lambda _ (fun j => ?_)
  unfold extAt
  by_cases h : j = k
  · simp only [h, dif_pos]; exact measurable_const
  · simp only [h, dif_neg, not_false_eq_true]; exact measurable_pi_apply _

lemma extAt_ne {ι α : Type*} [Fintype ι] [DecidableEq ι] (k : ι) (c : α) (x : ι → α) (j : ι)
    (hj : j ≠ k) : extAt k c (fun i : ↥(Finset.univ.erase k) => x i) j = x j := by
  simp [extAt, hj]

lemma iterFin_go_congr {T : ℕ} {S : Type} (s₀ : S) (step step' : Fin T → S → S) (τ : Fin T)
    (h : ∀ t, t ≠ τ → step t = step' t) :
    ∀ k, k ≤ τ.val → iterFin.go s₀ step k = iterFin.go s₀ step' k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    have hkT : k < T := by have := τ.isLt; omega
    simp only [iterFin.go, dif_pos hkT]
    rw [ih (by omega), h ⟨k, hkT⟩ (by intro he; rw [← he] at hk; simp at hk)]

lemma iterFin_succ {T : ℕ} {S : Type} (s₀ : S) (step : Fin T → S → S) (k : ℕ) (hk : k < T) :
    iterFin s₀ step (⟨k + 1, Nat.succ_lt_succ hk⟩ : Fin (T + 1)) =
      step ⟨k, hk⟩ (iterFin s₀ step (⟨k, Nat.lt_succ_of_lt hk⟩ : Fin (T + 1))) := by
  show iterFin.go s₀ step (k + 1) = _
  simp only [iterFin.go, dif_pos hk]
  rfl

lemma prob_section_eq {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β] {P : Measure Ω}
    [IsProbabilityMeasure P] {ξ : Ω → I} (hξ : Measurable ξ) (hlaw : P.map ξ = volume)
    {G : Ω → β} (hG : Measurable G) (hind : IndepFun G ξ P) {S : Set (β × I)}
    (hS : MeasurableSet S) :
    P {ω | (G ω, ξ ω) ∈ S} = ∫⁻ ω, volume {z | (G ω, z) ∈ S} ∂P := by
  have h1 : P {ω | (G ω, ξ ω) ∈ S} = (P.map (fun ω => (G ω, ξ ω))) S := by
    rw [Measure.map_apply (hG.prodMk hξ) hS]; rfl
  rw [h1, (indepFun_iff_map_prod_eq_prod_map_map hG.aemeasurable hξ.aemeasurable).1 hind, hlaw,
    Measure.prod_apply hS, lintegral_map (measurable_measure_prodMk_left hS) hG]
  rfl

section
variable {T : ℕ} {X Γ : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    [MeasurableSpace X] [DiscreteMeasurableSpace X]
    [Fintype Γ] [MeasurableSpace Γ] [DiscreteMeasurableSpace Γ]

lemma nLaw_map_noise {N : ℕ} (mN : ProbabilityMeasure (Fin N → X))
    (γ : ProbabilityMeasure (Fin N → Strat T X Γ)) (τ : Fin T) (j : Fin N) :
    (nLaw mN γ).map (fun ω => ω.2.2 τ j) = volume := by
  unfold nLaw
  have : (fun ω : NOmega T N X Γ => ω.2.2 τ j) =
      ((fun v : Fin N → I => v j) ∘ (fun ξ : Fin T → Fin N → I => ξ τ)) ∘ Prod.snd ∘ Prod.snd := rfl
  rw [this, ← Measure.map_map (((measurable_pi_apply j).comp (measurable_pi_apply τ)))
      (measurable_snd.comp measurable_snd), ← Measure.map_map measurable_snd measurable_snd,
    Measure.map_snd_prod]
  simp only [measure_univ, one_smul]
  rw [Measure.map_snd_prod]
  simp only [measure_univ, one_smul]
  rw [← Measure.map_map (measurable_pi_apply j) (measurable_pi_apply τ),
    (measurePreserving_eval _ τ).map_eq, (measurePreserving_eval _ j).map_eq]

lemma distTV_nonneg (m m' : Meas X) : 0 ≤ distTV m m' := by
  unfold distTV
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => abs_nonneg _)

lemma sum_abs_sub_le_two (p q : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hp1 : ∑ x, p x = 1) (hq1 : ∑ x, q x = 1) : ∑ x, |p x - q x| ≤ 2 := by
  have h1 : ∑ x, |p x - q x| ≤ ∑ x, (p x + q x) := by
    gcongr with x
    have := hp x; have := hq x
    rw [abs_le]; constructor <;> linarith
  rw [Finset.sum_add_distrib, hp1, hq1] at h1
  linarith

lemma distTV_le_one (m m' : Meas X) : distTV m m' ≤ 1 := by
  show (1 / 2 : ℝ) * ∑ x, |m.1 x - m'.1 x| ≤ 1
  have := sum_abs_sub_le_two m.1 m'.1 m.2.1 m'.2.1 m.2.2 m'.2.2
  linarith

lemma eq_of_distTV_eq_zero (m m' : Meas X) (h : distTV m m' = 0) : m = m' := by
  unfold distTV at h
  have hs : ∑ x, |(m : X → ℝ) x - (m' : X → ℝ) x| = 0 := by linarith
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => abs_nonneg _)] at hs
  apply Subtype.ext; funext x
  have := hs x (Finset.mem_univ _)
  rw [abs_eq_zero, sub_eq_zero] at this
  exact this

lemma psi_bound [TopologicalSpace X] [TopologicalSpace Γ] (M : Model T X Γ) (hA1a : M.A1a)
    (δ' : ℝ) (hδ' : 0 < δ') :
    ∃ δ > 0, ∀ (τ : Fin T) (x : X) (a : Γ) (m m' : Meas X),
      (volume : Measure I) {z | M.Ψ τ x m a z ≠ M.Ψ τ x m' a z} ≤
        ENNReal.ofReal (δ' + distTV m m' / δ) := by
  obtain ⟨w, -, hw01, hwlim, hwb⟩ := hA1a
  rw [Metric.tendsto_nhdsWithin_nhds] at hwlim
  obtain ⟨δ, hδ, hδw⟩ := hwlim δ' hδ'
  refine ⟨δ, hδ, fun τ x a m m' => ?_⟩
  set s := distTV m m' with hs
  have hs0 : 0 ≤ s := distTV_nonneg m m'
  rcases eq_or_lt_of_le hs0 with h0 | hpos
  · have : m = m' := eq_of_distTV_eq_zero m m' h0.symm
    subst this
    simp
  refine (hwb τ x a m m').trans (ENNReal.ofReal_le_ofReal ?_)
  rw [← hs]
  by_cases hsd : s < δ
  · have := hδw (Set.mem_Ioi.mpr hpos) (by rw [Real.dist_eq, sub_zero, abs_of_pos hpos]; exact hsd)
    rw [Real.dist_eq, sub_zero] at this
    have := (abs_lt.mp this).2
    have : 0 ≤ s / δ := div_nonneg hs0 hδ.le
    linarith
  · push_neg at hsd
    have h1 : 1 ≤ s / δ := by rw [le_div_iff₀ hδ]; linarith
    have := (hw01 s hs0).2
    linarith

end
end lib2

section main62
variable {T : ℕ} {X Γ : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    [MeasurableSpace X] [DiscreteMeasurableSpace X]
    [Fintype Γ] [MeasurableSpace Γ] [DiscreteMeasurableSpace Γ]

lemma hatPath_noise_congr (M : Model T X Γ) {N : ℕ} [NeZero N] (ω ω' : NOmega T N X Γ)
    (h1 : ω.1 = ω'.1) (h2 : ω.2.1 = ω'.2.1) (τ : Fin T) (h3 : ∀ s, s ≠ τ → ω.2.2 s = ω'.2.2 s)
    (t : Fin (T + 1)) (ht : t.val ≤ τ.val) : hatPath M ω t = hatPath M ω' t := by
  unfold hatPath iterFin
  rw [h1]
  apply iterFin_go_congr _ _ _ τ _ t.val ht
  intro s hs
  rw [h2, h3 s hs]

lemma nPath_noise_congr (M : Model T X Γ) {N : ℕ} (i : Fin N) (u : Strat T X Γ → Strat T X Γ)
    (ω ω' : NOmega T N X Γ)
    (h1 : ω.1 = ω'.1) (h2 : ω.2.1 = ω'.2.1) (τ : Fin T) (h3 : ∀ s, s ≠ τ → ω.2.2 s = ω'.2.2 s)
    (t : Fin (T + 1)) (ht : t.val ≤ τ.val) : nPath M i u ω t = nPath M i u ω' t := by
  unfold nPath iterFin
  rw [h1]
  apply iterFin_go_congr _ _ _ τ _ t.val ht
  intro s hs
  rw [h2, h3 s hs]

lemma step_bound [TopologicalSpace X] [TopologicalSpace Γ] (M : Model T X Γ) (hM : M.Standing)
    (u : Strat T X Γ → Strat T X Γ) {N : ℕ} [NeZero N]
    (mN : ProbabilityMeasure (Fin N → X)) (γ : ProbabilityMeasure (Fin N → Strat T X Γ))
    (k : ℕ) (hk : k < T) (δ' δ : ℝ) (hδ : 0 < δ) (hδ' : 0 ≤ δ')
    (hψ : ∀ (τ : Fin T) (x : X) (a : Γ) (m m' : Meas X),
      (volume : Measure I) {z | M.Ψ τ x m a z ≠ M.Ψ τ x m' a z} ≤
        ENNReal.ofReal (δ' + distTV m m' / δ))
    (j : Fin N) (hj : j ≠ 0) :
    (nLaw mN γ).real {ω | hatPath M ω ⟨k + 1, Nat.succ_lt_succ hk⟩ j ≠
        tildePath M u ω ⟨k + 1, Nat.succ_lt_succ hk⟩ j} ≤
      (nLaw mN γ).real {ω | hatPath M ω ⟨k, Nat.lt_succ_of_lt hk⟩ j ≠
        tildePath M u ω ⟨k, Nat.lt_succ_of_lt hk⟩ j} + δ' +
      (∫ ω, distTV (hatEmp M ω ⟨k, Nat.lt_succ_of_lt hk⟩)
        (tildeEmp M u ω j ⟨k, Nat.lt_succ_of_lt hk⟩) ∂(nLaw mN γ)) / δ := by
  set P := nLaw mN γ with hPdef
  set tk : Fin (T + 1) := ⟨k, Nat.lt_succ_of_lt hk⟩ with htk
  set τ : Fin T := ⟨k, hk⟩ with hτ
  -- the data at time `k` seen by player `j`
  set F : (Fin N → Strat T X Γ) × (Fin N → X) × (Fin N → X) → X × Meas X × Meas X × Γ :=
    fun q => (q.2.1 j, empOthers q.2.1 0, empOthers q.2.2 j, q.1 j τ (q.2.1 j)) with hF
  set G : NOmega T N X Γ → X × Meas X × Meas X × Γ :=
    fun ω => F (ω.2.1, hatPath M ω tk, tildePath M u ω tk) with hG
  have hGm : Measurable G := by
    refine (measurable_of_countable F).comp ?_
    exact (measurable_fst.comp measurable_snd).prodMk
      ((measurable_hatPath M hM tk).prodMk (measurable_nPath M hM 0 u tk))
  set S : Set ((X × Meas X × Meas X × Γ) × I) :=
    {p | M.Ψ τ p.1.1 p.1.2.1 p.1.2.2.2 p.2 ≠ M.Ψ τ p.1.1 p.1.2.2.1 p.1.2.2.2 p.2} with hS
  have hSm : MeasurableSet S := by
    have h1 : Measurable (fun p : (X × Meas X × Meas X × Γ) × I =>
        M.Ψ τ p.1.1 p.1.2.1 p.1.2.2.2 p.2) :=
      (hM.1 τ).comp ((measurable_fst.comp measurable_fst).prodMk
        ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk
          ((measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_fst))).prodMk
            measurable_snd)))
    have h2 : Measurable (fun p : (X × Meas X × Meas X × Γ) × I =>
        M.Ψ τ p.1.1 p.1.2.2.1 p.1.2.2.2 p.2) :=
      (hM.1 τ).comp ((measurable_fst.comp measurable_fst).prodMk
        ((measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_fst))).prodMk
          ((measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_fst))).prodMk
            measurable_snd)))
    exact (measurableSet_eq_fun h1 h2).compl
  have hξm : Measurable (fun ω : NOmega T N X Γ => ω.2.2 τ j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply τ).comp (measurable_snd.comp measurable_snd))
  -- independence of the noise `ξ_j(k+1)` from the data at time `k`
  have hind : IndepFun G (fun ω => ω.2.2 τ j) P := by
    have hI0 := indepFun_pi_at_rest (fun _ : Fin T => Measure.pi fun _ : Fin N => (volume : Measure I)) τ
    have hI1 := hI0.comp (measurable_pi_apply j) measurable_id
    have hrest : Measurable (fun (ξ : Fin T → Fin N → I) (s : ↥(Finset.univ.erase τ)) => ξ s) :=
      measurable_pi_lambda _ (fun s => measurable_pi_apply _)
    have hB1 := indepFun_prod_right (μ := (γ : Measure (Fin N → Strat T X Γ)))
      ((measurable_pi_apply j).comp (measurable_pi_apply τ)) (measurable_id.comp hrest) hI1
    have hB2 := indepFun_prod_right (μ := (mN : Measure (Fin N → X)))
      (((measurable_pi_apply j).comp (measurable_pi_apply τ)).comp measurable_snd)
      (measurable_fst.prodMk ((measurable_id.comp hrest).comp measurable_snd)) hB1
    set Gf : (Fin N → X) × ((Fin N → Strat T X Γ) × (↥(Finset.univ.erase τ) → Fin N → I)) →
        X × Meas X × Meas X × Γ :=
      fun q => G (q.1, q.2.1, extAt τ (fun _ => (0 : I)) q.2.2) with hGf
    have hGfm : Measurable Gf := hGm.comp (measurable_fst.prodMk
      ((measurable_fst.comp measurable_snd).prodMk ((measurable_extAt τ _).comp
        (measurable_snd.comp measurable_snd))))
    have h := hB2.comp measurable_id hGfm
    have h' : IndepFun (fun ω : NOmega T N X Γ => ω.2.2 τ j) G P := by
      refine h.congr (ae_of_all _ (fun ω => rfl)) (ae_of_all _ (fun ω => ?_))
      have hω : ∀ s, s ≠ τ → (extAt τ (fun _ => (0 : I))
          (fun s : ↥(Finset.univ.erase τ) => ω.2.2 s)) s = ω.2.2 s :=
        fun s hs => extAt_ne τ _ ω.2.2 s hs
      simp only [Function.comp_apply, id, hGf, hG]
      rw [hatPath_noise_congr M (ω.1, ω.2.1, extAt τ (fun _ => (0 : I))
          (fun s : ↥(Finset.univ.erase τ) => ω.2.2 s)) ω rfl rfl τ hω tk le_rfl,
        show tildePath M u (ω.1, ω.2.1, extAt τ (fun _ => (0 : I))
          (fun s : ↥(Finset.univ.erase τ) => ω.2.2 s)) tk = tildePath M u ω tk from
          nPath_noise_congr M 0 u (ω.1, ω.2.1, extAt τ (fun _ => (0 : I))
          (fun s : ↥(Finset.univ.erase τ) => ω.2.2 s)) ω rfl rfl τ hω tk le_rfl]
    exact h'.symm
  -- the union bound
  have hsub : {ω : NOmega T N X Γ | hatPath M ω ⟨k + 1, Nat.succ_lt_succ hk⟩ j ≠
        tildePath M u ω ⟨k + 1, Nat.succ_lt_succ hk⟩ j} ⊆
      {ω | hatPath M ω tk j ≠ tildePath M u ω tk j} ∪ {ω | (G ω, ω.2.2 τ j) ∈ S} := by
    intro ω hω
    by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
    obtain ⟨h1, h2⟩ := hc
    apply hω
    simp only [Set.mem_setOf_eq] at hω
    unfold hatPath tildePath nPath
    rw [iterFin_succ _ _ k hk, iterFin_succ _ _ k hk]
    simp only [hS, Set.mem_setOf_eq, not_not, hG, hF] at h2
    have hpl : played 0 u ω.2.1 j = ω.2.1 j := by simp [played, hj]
    rw [hpl]
    change hatPath M ω tk j = tildePath M u ω tk j at h1
    unfold tildePath nPath at h1
    unfold hatPath at h1 h2
    unfold tildePath nPath at h2
    rw [← h1]
    exact h2
  have hS'm : MeasurableSet {ω | (G ω, ω.2.2 τ j) ∈ S} := (hGm.prodMk hξm) hSm
  have hE0m : MeasurableSet {ω : NOmega T N X Γ | hatPath M ω tk j ≠ tildePath M u ω tk j} :=
    (measurableSet_eq_fun ((measurable_pi_apply j).comp (measurable_hatPath M hM tk))
      ((measurable_pi_apply j).comp (measurable_nPath M hM 0 u tk))).compl
  -- the Fubini bound
  set D : NOmega T N X Γ → ℝ := fun ω => distTV (hatEmp M ω tk) (tildeEmp M u ω j tk) with hD
  have hDm : Measurable D := by
    have : D = (fun q : (Fin N → X) × (Fin N → X) => distTV (empOthers q.1 0) (empOthers q.2 j)) ∘
        (fun ω => (hatPath M ω tk, tildePath M u ω tk)) := rfl
    rw [this]
    exact (measurable_of_countable _).comp ((measurable_hatPath M hM tk).prodMk
      (measurable_nPath M hM 0 u tk))
  have hDint : Integrable D P :=
    Integrable.of_bound hDm.aestronglyMeasurable 1 (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (distTV_nonneg _ _)]; exact distTV_le_one _ _)
  have hfint : Integrable (fun ω => δ' + D ω / δ) P :=
    (integrable_const δ').add (hDint.div_const δ)
  have hS'bound : P {ω | (G ω, ω.2.2 τ j) ∈ S} ≤ ∫⁻ ω, ENNReal.ofReal (δ' + D ω / δ) ∂P := by
    rw [prob_section_eq hξm (nLaw_map_noise mN γ τ j) hGm hind hSm]
    refine lintegral_mono fun ω => ?_
    exact hψ τ _ _ _ _
  have hS'real : P.real {ω | (G ω, ω.2.2 τ j) ∈ S} ≤ δ' + (∫ ω, D ω ∂P) / δ := by
    have hnn : 0 ≤ᵐ[P] (fun ω => δ' + D ω / δ) :=
      ae_of_all _ fun ω => add_nonneg hδ' (div_nonneg (distTV_nonneg _ _) hδ.le)
    have h1 : ∫ ω, (δ' + D ω / δ) ∂P = (∫⁻ ω, ENNReal.ofReal (δ' + D ω / δ) ∂P).toReal :=
      integral_eq_lintegral_of_nonneg_ae hnn hfint.aestronglyMeasurable
    have h2 : ∫ ω, (δ' + D ω / δ) ∂P = δ' + (∫ ω, D ω ∂P) / δ := by
      rw [integral_add (integrable_const δ') (hDint.div_const δ), integral_const, integral_div]
      simp
    rw [← h2, h1, measureReal_def]
    exact ENNReal.toReal_mono (by
      rw [← ofReal_integral_eq_lintegral_ofReal hfint hnn]; exact ENNReal.ofReal_ne_top) hS'bound
  calc P.real _ ≤ P.real ({ω | hatPath M ω tk j ≠ tildePath M u ω tk j} ∪
          {ω | (G ω, ω.2.2 τ j) ∈ S}) := measureReal_mono hsub
    _ ≤ P.real {ω | hatPath M ω tk j ≠ tildePath M u ω tk j} +
          P.real {ω | (G ω, ω.2.2 τ j) ∈ S} := measureReal_union_le _ _
    _ ≤ _ := by rw [add_assoc]; gcongr

end main62

theorem solution {T : ℕ} {X Γ : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    [TopologicalSpace X] [DiscreteTopology X] [MeasurableSpace X] [DiscreteMeasurableSpace X]
    [Fintype Γ] [Nonempty Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] [MeasurableSpace Γ]
    [DiscreteMeasurableSpace Γ]
    (M : Model T X Γ) (hM : M.Standing) (hA1a : M.A1a) (u : Strat T X Γ → Strat T X Γ)
    (mN : (n : ℕ) → ProbabilityMeasure (Fin (n + 2) → X))
    (γ : (n : ℕ) → ProbabilityMeasure (Fin (n + 2) → Strat T X Γ)) (t : Fin (T + 1)) :
    Tendsto (fun n : ℕ => (1 / ((n + 1 : ℕ) : ℝ)) *
        ∑ j ∈ Finset.univ.erase (0 : Fin (n + 2)),
          (nLaw (mN n) (γ n)).real {ω | hatPath M ω t j ≠ tildePath M u ω t j})
      atTop (𝓝 0) := by
  set a : ℕ → Fin (T + 1) → ℝ := fun n t => (1 / ((n + 1 : ℕ) : ℝ)) *
    ∑ j ∈ Finset.univ.erase (0 : Fin (n + 2)),
      (nLaw (mN n) (γ n)).real {ω | hatPath M ω t j ≠ tildePath M u ω t j} with ha
  have ha0 : ∀ n t, 0 ≤ a n t := fun n t =>
    mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => measureReal_nonneg)
  have hcard : ∀ n : ℕ, ((Finset.univ.erase (0 : Fin (n + 2))).card : ℝ) = ((n + 1 : ℕ) : ℝ) := by
    intro n
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    norm_num
  suffices key : ∀ k (hk : k < T + 1), Tendsto (fun n => a n ⟨k, hk⟩) atTop (𝓝 0) from
    key t.val t.isLt
  intro k
  induction k with
  | zero =>
    intro hk
    have : ∀ n, a n ⟨0, hk⟩ = 0 := by
      intro n
      simp only [ha]
      apply mul_eq_zero_of_right
      apply Finset.sum_eq_zero
      intro j _
      have : {ω : NOmega T (n + 2) X Γ | hatPath M ω ⟨0, hk⟩ j ≠ tildePath M u ω ⟨0, hk⟩ j} = ∅ := by
        ext ω; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]; rfl
      rw [this, measureReal_empty]
    simp_rw [this]
    exact tendsto_const_nhds
  | succ k ih =>
    intro hk
    have hkT : k < T := by omega
    have ih' := ih (Nat.lt_succ_of_lt hkT)
    have hc : Tendsto (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      simpa using this
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨δ, hδ, hψ⟩ := psi_bound M hA1a (ε / 2) (by positivity)
    -- the one-step recursion
    have hrec : ∀ n, a n ⟨k + 1, hk⟩ ≤ a n ⟨k, Nat.lt_succ_of_lt hkT⟩ + ε / 2 +
        (1 / ((n + 1 : ℕ) : ℝ) + a n ⟨k, Nat.lt_succ_of_lt hkT⟩) / δ := by
      intro n
      have hN : 2 ≤ n + 2 := by omega
      set c : ℝ := 1 / ((n + 1 : ℕ) : ℝ) with hcdef
      have hcpos : 0 < c := by positivity
      have hj : ∀ j ∈ Finset.univ.erase (0 : Fin (n + 2)),
          (nLaw (mN n) (γ n)).real {ω | hatPath M ω ⟨k + 1, hk⟩ j ≠ tildePath M u ω ⟨k + 1, hk⟩ j} ≤
          (nLaw (mN n) (γ n)).real {ω | hatPath M ω ⟨k, Nat.lt_succ_of_lt hkT⟩ j ≠
            tildePath M u ω ⟨k, Nat.lt_succ_of_lt hkT⟩ j} + ε / 2 +
          (c + a n ⟨k, Nat.lt_succ_of_lt hkT⟩) / δ := by
        intro j hjm
        have hj0 : j ≠ 0 := (Finset.mem_erase.mp hjm).1
        have h1 := step_bound M hM u (mN n) (γ n) k hkT (ε / 2) δ hδ (by positivity) hψ j hj0
        have h2 := eq_6_3 M hM u hN (mN n) (γ n) j ⟨k, Nat.lt_succ_of_lt hkT⟩
        have hNsub : ((n + 2 - 1 : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) := by
          congr 1
        rw [hNsub] at h2
        refine h1.trans ?_
        gcongr
      calc a n ⟨k + 1, hk⟩ = c * ∑ j ∈ Finset.univ.erase (0 : Fin (n + 2)),
            (nLaw (mN n) (γ n)).real {ω | hatPath M ω ⟨k + 1, hk⟩ j ≠ tildePath M u ω ⟨k + 1, hk⟩ j} :=
            rfl
        _ ≤ c * ∑ j ∈ Finset.univ.erase (0 : Fin (n + 2)),
            ((nLaw (mN n) (γ n)).real {ω | hatPath M ω ⟨k, Nat.lt_succ_of_lt hkT⟩ j ≠
              tildePath M u ω ⟨k, Nat.lt_succ_of_lt hkT⟩ j} + ε / 2 +
            (c + a n ⟨k, Nat.lt_succ_of_lt hkT⟩) / δ) := by
            gcongr with j hjm
            exact hj j hjm
        _ = a n ⟨k, Nat.lt_succ_of_lt hkT⟩ + c * ((n + 1 : ℕ) : ℝ) *
            (ε / 2 + (c + a n ⟨k, Nat.lt_succ_of_lt hkT⟩) / δ) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const,
              nsmul_eq_mul, nsmul_eq_mul, hcard n]
            simp only [ha, hcdef]
            ring
        _ = _ := by
            have : c * ((n + 1 : ℕ) : ℝ) = 1 := by
              rw [hcdef]; field_simp
            rw [this]; ring
    -- the error terms vanish
    have hlim : Tendsto (fun n => a n ⟨k, Nat.lt_succ_of_lt hkT⟩ +
        (1 / ((n + 1 : ℕ) : ℝ) + a n ⟨k, Nat.lt_succ_of_lt hkT⟩) / δ) atTop (𝓝 0) := by
      have := ih'.add ((hc.add ih').div_const δ)
      simpa using this
    obtain ⟨N0, hN0⟩ := (Metric.tendsto_atTop.mp hlim) (ε / 2) (by positivity)
    refine ⟨N0, fun n hn => ?_⟩
    have h1 := hN0 n hn
    rw [Real.dist_eq, sub_zero] at h1 ⊢
    have h2 := hrec n
    have h3 := ha0 n ⟨k + 1, hk⟩
    have h4 := ha0 n ⟨k, Nat.lt_succ_of_lt hkT⟩
    rw [abs_of_nonneg h3]
    have h5 : 0 ≤ (1 / ((n + 1 : ℕ) : ℝ) + a n ⟨k, Nat.lt_succ_of_lt hkT⟩) / δ := by positivity
    rw [abs_of_nonneg (by linarith)] at h1
    linarith
