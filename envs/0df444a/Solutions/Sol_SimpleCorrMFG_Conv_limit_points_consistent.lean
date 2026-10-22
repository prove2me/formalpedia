-- Prove2me | solution 1 for SimpleCorrMFG.Conv.limit_points_consistent
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T07:20:15.953881+00:00
-- url     : https://prove2.me/submissions/f2100c5d-35df-4b30-a779-ce3ca9354ff6

import Mathlib
import Definitions.Def_SimpleCorrMFG_Conv_Model
import Definitions.Def_SimpleCorrMFG_Conv_NPlayer
import Definitions.Def_SimpleCorrMFG_Conv_MFG
import Definitions.Def_SimpleCorrMFG_Conv_Coupling
import Theorems.Thm_SimpleCorrMFG_Conv_eq_6_3
import Theorems.Thm_SimpleCorrMFG_Conv_eq_6_2
import Theorems.Thm_SimpleCorrMFG_Conv_step_three_independence

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


end

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

lemma psi_bound (M : Model T X Γ) (hA1a : M.A1a)
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

lemma step_bound (M : Model T X Γ) (hM : M.Standing)
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

lemma empOn_apply' {X : Type} [Fintype X] [DecidableEq X] [Nonempty X] {ι : Type}
    (S : Finset ι) (hS : S.Nonempty) (x : ι → X) (y : X) :
    (empOn S x).1 y = (1 / (S.card : ℝ)) * ∑ j ∈ S, (if x j = y then (1 : ℝ) else 0) := by
  rw [empOn, dif_pos hS]
  show (∑ j ∈ S, if x j = y then (1:ℝ) else 0) / (S.card : ℝ) = _
  ring

lemma distTV_empOn_le {X : Type} [Fintype X] [DecidableEq X] [Nonempty X] {ι : Type}
    (S : Finset ι) (hS : S.Nonempty) (x x' : ι → X) :
    distTV (empOn S x) (empOn S x') ≤
      (1 / (S.card : ℝ)) * ∑ i ∈ S, (if x i ≠ x' i then (1 : ℝ) else 0) := by
  unfold distTV
  show (1 / 2 : ℝ) * ∑ y, |(empOn S x).1 y - (empOn S x').1 y| ≤ _
  simp_rw [empOn_apply' S hS]
  have hNpos : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have key : ∀ y : X, |(1 / (S.card : ℝ)) * ∑ i ∈ S, (if x i = y then (1 : ℝ) else 0) -
      (1 / (S.card : ℝ)) * ∑ i ∈ S, (if x' i = y then (1 : ℝ) else 0)| ≤
      (1 / (S.card : ℝ)) * ∑ i ∈ S, |(if x i = y then (1 : ℝ) else 0) - (if x' i = y then (1 : ℝ) else 0)| := by
    intro y
    rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_pos (by positivity)]
    gcongr
    exact Finset.abs_sum_le_sum_abs _ _
  have key2 : ∀ i : ι, ∑ y : X, |(if x i = y then (1 : ℝ) else 0) - (if x' i = y then (1 : ℝ) else 0)|
      = 2 * (if x i ≠ x' i then (1 : ℝ) else 0) := by
    intro i
    by_cases h : x i = x' i
    · simp [h]
    · simp only [ne_eq, h, not_false_eq_true, if_true]
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (x i)),
        ← Finset.sum_erase_add _ _ (Finset.mem_erase.mpr ⟨Ne.symm h, Finset.mem_univ (x' i)⟩)]
      rw [Finset.sum_eq_zero]
      · simp [h, Ne.symm h]; norm_num
      · intro y hy
        have h1 : y ≠ x' i := (Finset.mem_erase.mp hy).1
        have h2 : y ≠ x i := (Finset.mem_erase.mp (Finset.mem_erase.mp hy).2).1
        simp [Ne.symm h1, Ne.symm h2]
  calc (1 / 2 : ℝ) * ∑ y, |(1 / (S.card : ℝ)) * ∑ i ∈ S, (if x i = y then (1 : ℝ) else 0) -
      (1 / (S.card : ℝ)) * ∑ i ∈ S, (if x' i = y then (1 : ℝ) else 0)|
      ≤ (1 / 2 : ℝ) * ∑ y : X, (1 / (S.card : ℝ)) * ∑ i ∈ S,
          |(if x i = y then (1 : ℝ) else 0) - (if x' i = y then (1 : ℝ) else 0)| := by
        gcongr with y; exact key y
    _ = (1 / (S.card : ℝ)) * ∑ i ∈ S, (if x i ≠ x' i then (1 : ℝ) else 0) := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp_rw [key2]
        rw [← Finset.mul_sum]; ring

/-- Relabelling: `empOn` over `S` of `x ∘ e` equals `empOn` over `S'` of `x` when `e` maps `S` onto `S'`. -/
lemma empOn_comp_equiv {X : Type} [Fintype X] [DecidableEq X] [Nonempty X] {ι : Type}
    (S S' : Finset ι) (e : ι ≃ ι) (he : ∀ i, i ∈ S ↔ e i ∈ S') (x : ι → X) :
    empOn S (x ∘ e) = empOn S' x := by
  have hsum : ∀ g : ι → ℝ, ∑ j ∈ S, g (e j) = ∑ j ∈ S', g j := fun g =>
    Finset.sum_equiv e he (fun _ _ => rfl)
  have hcard : S.card = S'.card := Finset.card_equiv e he
  by_cases hS : S.Nonempty
  · have hS' : S'.Nonempty := by
      obtain ⟨i, hi⟩ := hS; exact ⟨e i, (he i).1 hi⟩
    apply Subtype.ext; funext y
    show (empOn S (x ∘ e)).1 y = (empOn S' x).1 y
    rw [empOn_apply' S hS, empOn_apply' S' hS', hcard]
    congr 1
    exact hsum (fun j => if x j = y then (1:ℝ) else 0)
  · have hS' : ¬ S'.Nonempty := by
      rintro ⟨i, hi⟩; exact hS ⟨e.symm i, (he _).2 (by simpa using hi)⟩
    simp only [empOn, dif_neg hS, dif_neg hS']


lemma pi_map_comp_perm {ι α : Type} [Fintype ι] [DecidableEq ι] [MeasurableSpace α] (μ : Measure α)
    [SigmaFinite μ] (e : Equiv.Perm ι) :
    (Measure.pi fun _ : ι => μ).map (fun x => x ∘ e) = Measure.pi fun _ : ι => μ := by
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply (show Measurable (fun x : ι → α => x ∘ e) from
    measurable_pi_lambda _ (fun i => measurable_pi_apply (e i))) (MeasurableSet.univ_pi hs)]
  have : (fun x : ι → α => x ∘ e) ⁻¹' Set.univ.pi s = Set.univ.pi (fun i => s (e.symm i)) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ_pi, Function.comp_apply]
    constructor
    · intro h i; simpa using h (e.symm i)
    · intro h i; simpa using h (e i)
  rw [this, Measure.pi_pi]
  exact Equiv.prod_comp e.symm (fun i => μ (s i))

section
variable {T : ℕ} {X Γ : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    [MeasurableSpace X] [DiscreteMeasurableSpace X]
    [Fintype Γ] [MeasurableSpace Γ] [DiscreteMeasurableSpace Γ]

/-- Relabel the players of a sample point by the permutation `e`. -/
def permΩ {N : ℕ} (e : Equiv.Perm (Fin N)) (ω : NOmega T N X Γ) : NOmega T N X Γ :=
  (ω.1 ∘ e, ω.2.1 ∘ e, fun t => ω.2.2 t ∘ e)

lemma measurable_permΩ {N : ℕ} (e : Equiv.Perm (Fin N)) :
    Measurable (permΩ (T := T) (X := X) (Γ := Γ) e) := by
  unfold permΩ
  refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)
  · exact (measurable_pi_lambda _ (fun i => measurable_pi_apply (e i))).comp measurable_fst
  · exact (measurable_pi_lambda _ (fun i => measurable_pi_apply (e i))).comp
      (measurable_fst.comp measurable_snd)
  · exact measurable_pi_lambda _ (fun t => measurable_pi_lambda _ (fun i =>
      (measurable_pi_apply (e i)).comp ((measurable_pi_apply t).comp
        (measurable_snd.comp measurable_snd))))

lemma nLaw_map_permΩ {N : ℕ} (m : Meas X) (γ : ProbabilityMeasure (Fin N → Strat T X Γ))
    (hγ : IsSymmetric γ) (e : Equiv.Perm (Fin N)) :
    (nLaw (prodInit N m) γ).map (permΩ e) = nLaw (prodInit N m) γ := by
  have hpe : ∀ {β : Type} [MeasurableSpace β], Measurable (fun x : Fin N → β => x ∘ e) :=
    fun {β} _ => measurable_pi_lambda _ (fun i => measurable_pi_apply (e i))
  have hnoise : Measurable (fun ξ : Fin T → Fin N → I => fun t => ξ t ∘ e) :=
    measurable_pi_lambda _ (fun t => hpe.comp (measurable_pi_apply t))
  have h1 : ((prodInit N m : ProbabilityMeasure (Fin N → X)) : Measure (Fin N → X)).map
      (fun x => x ∘ e) = (prodInit N m : Measure (Fin N → X)) := by
    simp only [prodInit, ProbabilityMeasure.coe_mk]
    exact pi_map_comp_perm _ e
  have h2 : (γ : Measure (Fin N → Strat T X Γ)).map (fun φ => φ ∘ e) = γ := hγ e
  have h3 : (Measure.pi fun _ : Fin T => Measure.pi fun _ : Fin N => (volume : Measure I)).map
      (fun ξ t => ξ t ∘ e) = Measure.pi fun _ : Fin T => Measure.pi fun _ : Fin N => (volume : Measure I) := by
    rw [Measure.pi_map_pi (fun _ => hpe.aemeasurable)]
    simp_rw [pi_map_comp_perm]
  unfold nLaw
  have : permΩ (T := T) (X := X) (Γ := Γ) e =
      Prod.map (fun x : Fin N → X => x ∘ e) (Prod.map (fun φ : Fin N → Strat T X Γ => φ ∘ e)
        (fun ξ : Fin T → Fin N → I => fun t => ξ t ∘ e)) := rfl
  rw [this, ← Measure.map_prod_map _ _ hpe (hpe.prodMap hnoise), ← Measure.map_prod_map _ _ hpe hnoise,
    h1, h2, h3]

lemma played_zero_id {N : ℕ} [NeZero N] (φ : Fin N → Strat T X Γ) (j : Fin N) :
    played 0 id φ j = φ j := by
  unfold played; split_ifs <;> rfl

lemma empOthers_comp_perm {N : ℕ} (x : Fin N → X) (e : Equiv.Perm (Fin N)) (j : Fin N) :
    empOthers (x ∘ e) j = empOthers x (e j) := by
  unfold empOthers
  apply empOn_comp_equiv
  intro i; simp

lemma nPath_permΩ (M : Model T X Γ) {N : ℕ} [NeZero N] (e : Equiv.Perm (Fin N))
    (ω : NOmega T N X Γ) (t : Fin (T + 1)) :
    nPath M 0 id (permΩ e ω) t = nPath M 0 id ω t ∘ e := by
  unfold nPath iterFin
  generalize t.val = k
  induction k with
  | zero => rfl
  | succ k ih =>
    by_cases hk : k < T
    · simp only [iterFin.go, dif_pos hk]
      rw [ih]
      funext j
      simp only [Function.comp_apply, played_zero_id, empOthers_comp_perm]
      rfl
    · simp only [iterFin.go, dif_neg hk]
      exact ih

end


section B
variable {T : ℕ} {X Γ : Type} [Fintype X]

lemma distTV_nonneg' (m m' : Meas X) : 0 ≤ distTV m m' := by
  unfold distTV; exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => abs_nonneg _)

instance instCompactMeasOR : CompactSpace (Meas X) :=
  isCompact_iff_compactSpace.mp (isCompact_stdSimplex ℝ X)

lemma dist_meas_le_distTV (m m' : Meas X) : dist m m' ≤ 2 * distTV m m' := by
  rw [Subtype.dist_eq]
  have h0 : 0 ≤ 2 * distTV m m' := by
    unfold distTV; exact mul_nonneg (by norm_num) (mul_nonneg (by norm_num)
      (Finset.sum_nonneg fun _ _ => abs_nonneg _))
  refine (dist_pi_le_iff h0).2 fun x => ?_
  rw [Real.dist_eq]
  show |m.1 x - m'.1 x| ≤ 2 * ((1 / 2 : ℝ) * ∑ y, |m.1 y - m'.1 y|)
  have := Finset.single_le_sum (f := fun y => |m.1 y - m'.1 y|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ x)
  linarith

lemma dist_flow_le (μ μ' : Flow T X) : dist μ μ' ≤ 2 * ∑ t, distTV (μ t) (μ' t) := by
  have h0 : 0 ≤ 2 * ∑ t, distTV (μ t) (μ' t) := by
    refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun t _ => ?_)
    unfold distTV; exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  refine (dist_pi_le_iff h0).2 fun t => ?_
  refine (dist_meas_le_distTV _ _).trans ?_
  have := Finset.single_le_sum (f := fun s => distTV (μ s) (μ' s))
    (fun s _ => distTV_nonneg' _ _) (Finset.mem_univ t)
  linarith

/-- A finite family of continuous functions on the compact flow space is uniformly
equicontinuous. -/
lemma unif_family {ι : Type*} [Finite ι] (H : ι → Flow T X → ℝ) (hH : ∀ i, Continuous (H i))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ i μ μ', dist μ μ' < δ → |H i μ - H i μ'| < ε := by
  have hu : ∀ i, ∃ δ > 0, ∀ μ μ' : Flow T X, dist μ μ' < δ → dist (H i μ) (H i μ') < ε :=
    fun i => Metric.uniformContinuous_iff.mp
      (CompactSpace.uniformContinuous_of_continuous (hH i)) ε hε
  choose δ hδ hδH using hu
  cases isEmpty_or_nonempty ι with
  | inl h => exact ⟨1, one_pos, fun i => (IsEmpty.false i).elim⟩
  | inr h =>
    haveI := Fintype.ofFinite ι
    refine ⟨Finset.univ.inf' Finset.univ_nonempty δ, ?_, fun i μ μ' hd => ?_⟩
    · show 0 < _
      rw [Finset.lt_inf'_iff]; exact fun i _ => hδ i
    · have := hδH i μ μ' (lt_of_lt_of_le hd (Finset.inf'_le _ (Finset.mem_univ i)))
      rwa [Real.dist_eq] at this

/-- Pointwise Markov-type bound from equicontinuity and boundedness. -/
lemma unif_bound {ι : Type*} (H : ι → Flow T X → ℝ) (C : ℝ) (hC : ∀ i μ, |H i μ| ≤ C)
    (ε δ : ℝ) (hδ : 0 < δ) (hu : ∀ i μ μ', dist μ μ' < δ → |H i μ - H i μ'| < ε)
    (i : ι) (μ μ' : Flow T X) :
    |H i μ - H i μ'| ≤ ε + 2 * C * (2 * ∑ t, distTV (μ t) (μ' t)) / δ := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC i μ)
  have hd := dist_flow_le μ μ'
  by_cases h : dist μ μ' < δ
  · have := hu i μ μ' h
    have : 0 ≤ 2 * C * (2 * ∑ t, distTV (μ t) (μ' t)) / δ :=
      div_nonneg (mul_nonneg (by linarith) ((dist_nonneg).trans hd)) hδ.le
    linarith
  · push_neg at h
    have h1 : |H i μ - H i μ'| ≤ 2 * C := by
      have := abs_sub (H i μ) (H i μ'); have := hC i μ; have := hC i μ'; linarith
    have h2 : 1 ≤ (2 * ∑ t, distTV (μ t) (μ' t)) / δ := by
      rw [le_div_iff₀ hδ]; linarith
    have hε0 : 0 ≤ ε := (abs_nonneg _).trans (hu i μ μ (by simpa using hδ)).le
    calc |H i μ - H i μ'| ≤ 2 * C * 1 := by linarith
      _ ≤ 2 * C * ((2 * ∑ t, distTV (μ t) (μ' t)) / δ) := by gcongr
      _ ≤ _ := by
        have : 2 * C * ((2 * ∑ t, distTV (μ t) (μ' t)) / δ) =
          2 * C * (2 * ∑ t, distTV (μ t) (μ' t)) / δ := by ring
        linarith

end B

section C
variable {T : ℕ} {X Γ : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    [MeasurableSpace X] [DiscreteMeasurableSpace X]
    [Fintype Γ] [MeasurableSpace Γ] [DiscreteMeasurableSpace Γ]

lemma measurable_mfgPath (M : Model T X Γ) (hM : M.Standing) (u : Strat T X Γ → Strat T X Γ)
    (t : Fin (T + 1)) : Measurable (fun ω : MOmega T X Γ => mfgPath M u ω t) := by
  unfold mfgPath
  refine measurable_iterFin (fun ω : MOmega T X Γ => ω.1) measurable_fst
    (fun ω t x => M.Ψ t x (ω.2.1.2 t.castSucc) (u ω.2.1.1 t x) (ω.2.2 t)) (fun s x => ?_) t
  have hφ : Measurable (fun ω : MOmega T X Γ => u ω.2.1.1 s x) :=
    (measurable_of_countable (fun φ : Strat T X Γ => u φ s x)).comp
      (measurable_fst.comp (measurable_fst.comp measurable_snd))
  have hμ : Measurable (fun ω : MOmega T X Γ => ω.2.1.2 s.castSucc) :=
    (measurable_pi_apply _).comp (measurable_snd.comp (measurable_fst.comp measurable_snd))
  have hz : Measurable (fun ω : MOmega T X Γ => ω.2.2 s) :=
    (measurable_pi_apply s).comp (measurable_snd.comp measurable_snd)
  exact (hM.1 s).comp (measurable_const.prodMk (hμ.prodMk (hφ.prodMk hz)))

/-- The flow-continuous bounded test functionals. -/
structure GoodQ (T : ℕ) (X Γ : Type) [Fintype X] [TopologicalSpace Γ] where
  Q : (Fin (T + 1) → X) → Strat T X Γ → Flow T X → ℝ
  C : ℝ
  C_nonneg : 0 ≤ C
  bound : ∀ p φ μ, |Q p φ μ| ≤ C
  cont : ∀ p φ, Continuous (Q p φ)

variable [TopologicalSpace Γ] [DiscreteTopology Γ]

lemma GoodQ.measurable (G : GoodQ T X Γ) :
    Measurable (fun r : ((Fin (T + 1) → X) × Strat T X Γ) × Flow T X => G.Q r.1.1 r.1.2 r.2) :=
  measurable_from_prod_countable_right (fun pq => (G.cont pq.1 pq.2).measurable)

/-- `V(m, ρ) = E[Q(X(·), Φ, μ)]` in a realization of `(m, ρ, u)`. -/
noncomputable def VQ (M : Model T X Γ) (u : Strat T X Γ → Strat T X Γ) (G : GoodQ T X Γ)
    (m : Meas X) (ρ : ProbabilityMeasure (Strat T X Γ × Flow T X)) : ℝ :=
  ∫ ω, G.Q (mfgPath M u ω) ω.2.1.1 ω.2.1.2 ∂(mfgLaw m ρ)

/-- `H(x₀, φ, μ) = E_ξ[Q(X(·), φ, μ)]` for the path started at `x₀` with data `(φ, μ)`. -/
noncomputable def HQ (M : Model T X Γ) (u : Strat T X Γ → Strat T X Γ) (G : GoodQ T X Γ)
    (x₀ : X) (q : Strat T X Γ × Flow T X) : ℝ :=
  ∫ ξ, G.Q (mfgPath M u (x₀, q, ξ)) q.1 q.2 ∂(Measure.pi fun _ : Fin T => (volume : Measure I))

lemma measurable_Qpath (M : Model T X Γ) (hM : M.Standing) (u : Strat T X Γ → Strat T X Γ)
    (G : GoodQ T X Γ) :
    Measurable (fun ω : MOmega T X Γ => G.Q (mfgPath M u ω) ω.2.1.1 ω.2.1.2) := by
  have hp : Measurable (fun ω : MOmega T X Γ => mfgPath M u ω) :=
    measurable_pi_lambda _ (fun t => measurable_mfgPath M hM u t)
  exact G.measurable.comp ((hp.prodMk (measurable_fst.comp (measurable_fst.comp measurable_snd))).prodMk
    (measurable_snd.comp (measurable_fst.comp measurable_snd)))

lemma toPM_real_singleton (m : Meas X) (x : X) :
    ((m.toPM : ProbabilityMeasure X) : Measure X).real {x} = (m : X → ℝ) x := by
  simp only [Meas.toPM, ProbabilityMeasure.coe_mk, measureReal_def]
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton x)]
  simp [PMF.ofFintype_apply, ENNReal.toReal_ofReal (m.2.1 x)]

lemma VQ_eq_sum (M : Model T X Γ) (hM : M.Standing) (u : Strat T X Γ → Strat T X Γ)
    (G : GoodQ T X Γ) (m : Meas X) (ρ : ProbabilityMeasure (Strat T X Γ × Flow T X)) :
    VQ M u G m ρ = ∑ x₀, (m : X → ℝ) x₀ *
      ∫ q, HQ M u G x₀ q ∂(ρ : Measure (Strat T X Γ × Flow T X)) := by
  have hF := measurable_Qpath M hM u G
  have hint : Integrable (fun ω : MOmega T X Γ => G.Q (mfgPath M u ω) ω.2.1.1 ω.2.1.2)
      (mfgLaw m ρ) :=
    Integrable.of_bound hF.aestronglyMeasurable G.C (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs]; exact G.bound _ _ _)
  unfold VQ mfgLaw
  rw [integral_prod _ hint]
  have h2 : ∀ x₀ : X, ∫ y, G.Q (mfgPath M u (x₀, y)) y.1.1 y.1.2
      ∂((ρ : Measure (Strat T X Γ × Flow T X)).prod
        (Measure.pi fun _ : Fin T => (volume : Measure I))) =
      ∫ q, HQ M u G x₀ q ∂(ρ : Measure (Strat T X Γ × Flow T X)) := by
    intro x₀
    have hm : Measurable (fun y : (Strat T X Γ × Flow T X) × (Fin T → I) =>
        G.Q (mfgPath M u (x₀, y)) y.1.1 y.1.2) := hF.comp (measurable_const.prodMk measurable_id)
    rw [integral_prod _ (Integrable.of_bound hm.aestronglyMeasurable G.C (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs]; exact G.bound _ _ _))]
    rfl
  simp_rw [h2]
  have hint2 : Integrable (fun x₀ : X => ∫ q, HQ M u G x₀ q ∂(ρ : Measure (Strat T X Γ × Flow T X)))
      ((m.toPM : ProbabilityMeasure X) : Measure X) := Integrable.of_finite
  rw [integral_fintype hint2]
  simp_rw [toPM_real_singleton, smul_eq_mul]

end C

section D
variable {T : ℕ} {X Γ : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    [MeasurableSpace X] [DiscreteMeasurableSpace X]
    [Fintype Γ] [MeasurableSpace Γ] [DiscreteMeasurableSpace Γ]
    [TopologicalSpace Γ] [DiscreteTopology Γ]

lemma distTV_le_card_dist (m m' : Meas X) : distTV m m' ≤ Fintype.card X * dist m m' := by
  show (1 / 2 : ℝ) * ∑ x, |m.1 x - m'.1 x| ≤ _
  have h : ∀ x, |m.1 x - m'.1 x| ≤ dist m m' := by
    intro x
    rw [Subtype.dist_eq, ← Real.dist_eq]
    exact dist_le_pi_dist m.1 m'.1 x
  have h2 : ∑ x, |m.1 x - m'.1 x| ≤ ∑ _x : X, dist m m' := Finset.sum_le_sum fun x _ => h x
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h2
  have := dist_nonneg (x := m) (y := m')
  nlinarith

lemma HQ_abs_le (M : Model T X Γ) (u : Strat T X Γ → Strat T X Γ) (G : GoodQ T X Γ) (x₀ : X)
    (q : Strat T X Γ × Flow T X) : |HQ M u G x₀ q| ≤ G.C := by
  unfold HQ
  refine (abs_integral_le_integral_abs).trans ?_
  have : ∫ ξ, |G.Q (mfgPath M u (x₀, q, ξ)) q.1 q.2| ∂(Measure.pi fun _ : Fin T => (volume : Measure I))
      ≤ ∫ _ξ, G.C ∂(Measure.pi fun _ : Fin T => (volume : Measure I)) :=
    integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) (integrable_const _)
      (ae_of_all _ fun ξ => G.bound _ _ _)
  simpa using this

lemma mfgPath_congr_flow (M : Model T X Γ) (u : Strat T X Γ → Strat T X Γ) (x₀ : X)
    (φ : Strat T X Γ) (μ μ' : Flow T X) (ξ : Fin T → I)
    (h : ∀ (t : Fin T) (x : X) (a : Γ), M.Ψ t x (μ' t.castSucc) a (ξ t) = M.Ψ t x (μ t.castSucc) a (ξ t)) :
    mfgPath M u (x₀, (φ, μ'), ξ) = mfgPath M u (x₀, (φ, μ), ξ) := by
  unfold mfgPath
  congr 1
  funext t x
  exact h t x _

lemma HQ_continuous_flow (M : Model T X Γ) (hM : M.Standing) (hA1a : M.A1a)
    (u : Strat T X Γ → Strat T X Γ) (G : GoodQ T X Γ) (x₀ : X) (φ : Strat T X Γ) :
    Continuous (fun μ : Flow T X => HQ M u G x₀ (φ, μ)) := by
  rw [Metric.continuous_iff]
  intro μ ε hε
  set K : ℝ := (Fintype.card (Fin T × X × Γ) : ℝ) with hK
  have hK0 : 0 ≤ K := by positivity
  set c : ℝ := 2 * G.C with hc
  have hc0 : 0 ≤ c := by have := G.C_nonneg; positivity
  set δ' : ℝ := ε / (4 * (c * K + 1)) with hδ'
  have hδ'0 : 0 < δ' := by positivity
  obtain ⟨δ, hδ, hψ⟩ := psi_bound M hA1a δ' hδ'0
  obtain ⟨η1, hη1, hu⟩ := unif_family (fun p : Fin (T + 1) → X => G.Q p φ)
    (fun p => G.cont p φ) (ε / 4) (by positivity)
  set η2 : ℝ := ε * δ / (4 * (c * K * Fintype.card X + 1)) with hη2
  have hη20 : 0 < η2 := by positivity
  refine ⟨min η1 η2, lt_min hη1 hη20, fun μ' hμ' => ?_⟩
  have hd1 : dist μ' μ < η1 := lt_of_lt_of_le hμ' (min_le_left _ _)
  have hd2 : dist μ' μ < η2 := lt_of_lt_of_le hμ' (min_le_right _ _)
  set ν : Measure (Fin T → I) := Measure.pi fun _ : Fin T => (volume : Measure I) with hν
  -- the bad set
  set B : Fin T × X × Γ → Set (Fin T → I) := fun i =>
    {ξ | M.Ψ i.1 i.2.1 (μ' i.1.castSucc) i.2.2 (ξ i.1) ≠ M.Ψ i.1 i.2.1 (μ i.1.castSucc) i.2.2 (ξ i.1)}
    with hB
  have hZm : ∀ i : Fin T × X × Γ, MeasurableSet
      {z : I | M.Ψ i.1 i.2.1 (μ' i.1.castSucc) i.2.2 z ≠ M.Ψ i.1 i.2.1 (μ i.1.castSucc) i.2.2 z} := by
    intro i
    have h1 : Measurable (fun z : I => M.Ψ i.1 i.2.1 (μ' i.1.castSucc) i.2.2 z) :=
      (hM.1 i.1).comp (measurable_const.prodMk (measurable_const.prodMk
        (measurable_const.prodMk measurable_id)))
    have h2 : Measurable (fun z : I => M.Ψ i.1 i.2.1 (μ i.1.castSucc) i.2.2 z) :=
      (hM.1 i.1).comp (measurable_const.prodMk (measurable_const.prodMk
        (measurable_const.prodMk measurable_id)))
    exact (measurableSet_eq_fun h1 h2).compl
  have hBm : ∀ i, MeasurableSet (B i) := fun i => (hZm i).preimage (measurable_pi_apply i.1)
  have hBreal : ∀ i, ν.real (B i) ≤ δ' + distTV (μ' i.1.castSucc) (μ i.1.castSucc) / δ := by
    intro i
    have hpre : B i = (fun ξ : Fin T → I => ξ i.1) ⁻¹'
        {z | M.Ψ i.1 i.2.1 (μ' i.1.castSucc) i.2.2 z ≠ M.Ψ i.1 i.2.1 (μ i.1.castSucc) i.2.2 z} := rfl
    have hz := hZm i
    rw [hpre, measureReal_def, ← Measure.map_apply (measurable_pi_apply i.1) hz,
      (measurePreserving_eval (fun _ : Fin T => (volume : Measure I)) i.1).map_eq]
    have := hψ i.1 i.2.1 i.2.2 (μ' i.1.castSucc) (μ i.1.castSucc)
    have hnn : 0 ≤ δ' + distTV (μ' i.1.castSucc) (μ i.1.castSucc) / δ :=
      add_nonneg hδ'0.le (div_nonneg (distTV_nonneg' _ _) hδ.le)
    exact (ENNReal.toReal_le_of_le_ofReal hnn this)
  have hBad : ν.real (⋃ i, B i) ≤ K * (δ' + Fintype.card X * η2 / δ) := by
    refine (measureReal_iUnion_fintype_le B).trans ?_
    have : ∀ i, ν.real (B i) ≤ δ' + Fintype.card X * η2 / δ := by
      intro i
      refine (hBreal i).trans ?_
      gcongr
      refine (distTV_le_card_dist _ _).trans ?_
      gcongr
      exact (dist_le_pi_dist μ' μ _).trans hd2.le
    refine (Finset.sum_le_sum fun i _ => this i).trans ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- pointwise bound
  have hpt : ∀ ξ, |G.Q (mfgPath M u (x₀, (φ, μ'), ξ)) φ μ' - G.Q (mfgPath M u (x₀, (φ, μ), ξ)) φ μ|
      ≤ ε / 4 + c * (⋃ i, B i).indicator (fun _ => (1 : ℝ)) ξ := by
    intro ξ
    by_cases hξ : ξ ∈ ⋃ i, B i
    · rw [Set.indicator_of_mem hξ, mul_one]
      have h1 := hu (mfgPath M u (x₀, (φ, μ'), ξ)) μ' μ hd1
      have h2 : |G.Q (mfgPath M u (x₀, (φ, μ'), ξ)) φ μ - G.Q (mfgPath M u (x₀, (φ, μ), ξ)) φ μ| ≤ c := by
        have := abs_sub (G.Q (mfgPath M u (x₀, (φ, μ'), ξ)) φ μ) (G.Q (mfgPath M u (x₀, (φ, μ), ξ)) φ μ)
        have := G.bound (mfgPath M u (x₀, (φ, μ'), ξ)) φ μ
        have := G.bound (mfgPath M u (x₀, (φ, μ), ξ)) φ μ
        linarith
      have := abs_sub_le (G.Q (mfgPath M u (x₀, (φ, μ'), ξ)) φ μ') (G.Q (mfgPath M u (x₀, (φ, μ'), ξ)) φ μ)
        (G.Q (mfgPath M u (x₀, (φ, μ), ξ)) φ μ)
      linarith
    · rw [Set.indicator_of_notMem hξ, mul_zero, add_zero]
      have heq : mfgPath M u (x₀, (φ, μ'), ξ) = mfgPath M u (x₀, (φ, μ), ξ) := by
        apply mfgPath_congr_flow
        intro t x a
        by_contra hne
        exact hξ (Set.mem_iUnion.mpr ⟨(t, x, a), hne⟩)
      rw [heq]
      exact (hu _ μ' μ hd1).le
  -- integrate
  have hmQ : ∀ ν' : Flow T X, Measurable (fun ξ : Fin T → I => G.Q (mfgPath M u (x₀, (φ, ν'), ξ)) φ ν') := by
    intro ν'
    exact (measurable_Qpath M hM u G).comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have hiQ : ∀ ν' : Flow T X, Integrable (fun ξ : Fin T → I => G.Q (mfgPath M u (x₀, (φ, ν'), ξ)) φ ν') ν :=
    fun ν' => Integrable.of_bound (hmQ ν').aestronglyMeasurable G.C (ae_of_all _ fun ξ => by
      rw [Real.norm_eq_abs]; exact G.bound _ _ _)
  rw [Real.dist_eq]
  unfold HQ
  rw [← integral_sub (hiQ μ') (hiQ μ)]
  refine (abs_integral_le_integral_abs).trans_lt ?_
  have hind : Integrable (fun ξ => ε / 4 + c * (⋃ i, B i).indicator (fun _ => (1 : ℝ)) ξ) ν :=
    (integrable_const _).add (((integrable_const (1 : ℝ)).indicator (MeasurableSet.iUnion hBm)).const_mul c)
  calc ∫ ξ, |G.Q (mfgPath M u (x₀, (φ, μ'), ξ)) φ μ' - G.Q (mfgPath M u (x₀, (φ, μ), ξ)) φ μ| ∂ν
      ≤ ∫ ξ, (ε / 4 + c * (⋃ i, B i).indicator (fun _ => (1 : ℝ)) ξ) ∂ν :=
        integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) hind (ae_of_all _ hpt)
    _ = ε / 4 + c * ν.real (⋃ i, B i) := by
        rw [integral_add (integrable_const _) (((integrable_const (1 : ℝ)).indicator
          (MeasurableSet.iUnion hBm)).const_mul c), integral_const, integral_const_mul,
          integral_indicator (MeasurableSet.iUnion hBm), setIntegral_const]
        simp
    _ ≤ ε / 4 + c * (K * (δ' + Fintype.card X * η2 / δ)) := by gcongr
    _ < ε := by
        have e1 : c * (K * δ') ≤ ε / 4 := by
          rw [hδ']
          rw [show c * (K * (ε / (4 * (c * K + 1)))) = ε / 4 * (c * K / (c * K + 1)) by
            field_simp]
          have : c * K / (c * K + 1) ≤ 1 := by
            rw [div_le_one (by positivity)]; linarith
          nlinarith
        have e2 : c * (K * (Fintype.card X * η2 / δ)) ≤ ε / 4 := by
          rw [hη2]
          have hX : (0 : ℝ) ≤ Fintype.card X := by positivity
          rw [show c * (K * (Fintype.card X * (ε * δ / (4 * (c * K * Fintype.card X + 1))) / δ)) =
              ε / 4 * (c * K * Fintype.card X / (c * K * Fintype.card X + 1)) by
            field_simp]
          have : c * K * Fintype.card X / (c * K * Fintype.card X + 1) ≤ 1 := by
            rw [div_le_one (by positivity)]; linarith
          nlinarith
        nlinarith

lemma HQ_continuous (M : Model T X Γ) (hM : M.Standing) (hA1a : M.A1a)
    (u : Strat T X Γ → Strat T X Γ) (G : GoodQ T X Γ) (x₀ : X) :
    Continuous (fun q : Strat T X Γ × Flow T X => HQ M u G x₀ q) :=
  continuous_prod_of_discrete_left.mpr (fun φ => HQ_continuous_flow M hM hA1a u G x₀ φ)

end D

section E
variable {T : ℕ} {X Γ : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    [MeasurableSpace X] [DiscreteMeasurableSpace X]
    [Fintype Γ] [MeasurableSpace Γ] [DiscreteMeasurableSpace Γ]
    [TopologicalSpace Γ] [DiscreteTopology Γ]

lemma VQ_tendsto (M : Model T X Γ) (hM : M.Standing) (hA1a : M.A1a)
    (u : Strat T X Γ → Strat T X Γ) (G : GoodQ T X Γ) {m : ℕ → Meas X} {m₀ : Meas X}
    (hm : Tendsto m atTop (𝓝 m₀)) {ρs : ℕ → ProbabilityMeasure (Strat T X Γ × Flow T X)}
    {ρ : ProbabilityMeasure (Strat T X Γ × Flow T X)} (hρ : Tendsto ρs atTop (𝓝 ρ)) :
    Tendsto (fun k => VQ M u G (m k) (ρs k)) atTop (𝓝 (VQ M u G m₀ ρ)) := by
  simp_rw [VQ_eq_sum M hM u G]
  refine tendsto_finset_sum _ fun x₀ _ => ?_
  refine Tendsto.mul ?_ ?_
  · exact (((continuous_apply x₀).comp continuous_subtype_val).tendsto m₀).comp hm
  · let f : BoundedContinuousFunction (Strat T X Γ × Flow T X) ℝ :=
      BoundedContinuousFunction.mkOfBound ⟨fun q => HQ M u G x₀ q, HQ_continuous M hM hA1a u G x₀⟩
        (2 * G.C) (fun a b => by
          simp only [ContinuousMap.coe_mk, Real.dist_eq]
          have := abs_sub (HQ M u G x₀ a) (HQ M u G x₀ b)
          have := HQ_abs_le M u G x₀ a; have := HQ_abs_le M u G x₀ b
          linarith)
    have := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hρ) f
    exact this

lemma measurable_rhoMap (M : Model T X Γ) (hM : M.Standing) {N : ℕ} [NeZero N] :
    Measurable (rhoMap M (N := N)) := by
  unfold rhoMap
  refine Measurable.prodMk ((measurable_pi_apply 0).comp (measurable_fst.comp measurable_snd)) ?_
  refine measurable_pi_lambda _ (fun t => ?_)
  exact (measurable_of_countable (fun x : Fin N → X => empOthers x 0)).comp
    (measurable_nPath M hM 0 id t)

lemma rhoN_coe [Nonempty Γ] (M : Model T X Γ) (hM : M.Standing) {N : ℕ} [NeZero N]
    (mN : ProbabilityMeasure (Fin N → X)) (γ : ProbabilityMeasure (Fin N → Strat T X Γ)) :
    (rhoN M mN γ : Measure (Strat T X Γ × Flow T X)) = (nLaw mN γ).map (rhoMap M) := by
  have h : AEMeasurable (rhoMap M) (nLaw mN γ) := by exact (measurable_rhoMap M hM).aemeasurable
  have : rhoN M mN γ = ⟨(nLaw mN γ).map (rhoMap M), Measure.isProbabilityMeasure_map h⟩ := by
    unfold rhoN; exact dif_pos h
  rw [this]; rfl

/-- The decoupled data of player `1` (index `0`). -/
noncomputable def Θ (M : Model T X Γ) {N : ℕ} [NeZero N] (ω : NOmega T N X Γ) : MOmega T X Γ :=
  (ω.1 0, (ω.2.1 0, fun t => hatEmp M ω t), fun t => ω.2.2 t 0)

lemma measurable_Θ (M : Model T X Γ) (hM : M.Standing) {N : ℕ} [NeZero N] :
    Measurable (Θ M (N := N)) := by
  unfold Θ
  refine Measurable.prodMk ((measurable_pi_apply 0).comp measurable_fst) (Measurable.prodMk ?_ ?_)
  · exact ((measurable_pi_apply 0).comp (measurable_fst.comp measurable_snd)).prodMk
      (measurable_pi_lambda _ (fun t => measurable_hatEmp M hM t))
  · exact measurable_pi_lambda _ (fun t => (measurable_pi_apply 0).comp
      ((measurable_pi_apply t).comp (measurable_snd.comp measurable_snd)))

/-- The law of `(Φ_1, μ̂_1(·))`. -/
noncomputable def rhoHat (M : Model T X Γ) (hM : M.Standing) {N : ℕ} [NeZero N]
    (mN : ProbabilityMeasure (Fin N → X)) (γ : ProbabilityMeasure (Fin N → Strat T X Γ)) :
    ProbabilityMeasure (Strat T X Γ × Flow T X) :=
  ⟨(nLaw mN γ).map (fun ω => (ω.2.1 0, fun t => hatEmp M ω t)),
    Measure.isProbabilityMeasure_map (((measurable_pi_apply 0).comp
      (measurable_fst.comp measurable_snd)).prodMk
      (measurable_pi_lambda _ (fun t => measurable_hatEmp M hM t))).aemeasurable⟩

lemma nLaw_map_Θ [TopologicalSpace X] [DiscreteTopology X] [Nonempty Γ]
    (M : Model T X Γ) (hM : M.Standing) {N : ℕ} [NeZero N] (hN : 2 ≤ N) (m : Meas X)
    (γ : ProbabilityMeasure (Fin N → Strat T X Γ)) :
    (nLaw (prodInit N m) γ).map (Θ M) = mfgLaw m (rhoHat M hM (prodInit N m) γ) := by
  set P := nLaw (prodInit N m) γ with hP
  have h3 := step_three_independence M hM hN m γ
  set A : NOmega T N X Γ → X := fun ω => ω.1 0 with hA
  set Bξ : NOmega T N X Γ → (Fin T → I) := fun ω t => ω.2.2 t 0 with hBξ
  set R : NOmega T N X Γ → Strat T X Γ × Flow T X :=
    fun ω => (ω.2.1 0, fun t => hatEmp M ω t) with hR
  have hAm : Measurable A := (measurable_pi_apply 0).comp measurable_fst
  have hBm : Measurable Bξ := measurable_pi_lambda _ (fun t => (measurable_pi_apply 0).comp
      ((measurable_pi_apply t).comp (measurable_snd.comp measurable_snd)))
  have hRm : Measurable R := ((measurable_pi_apply 0).comp (measurable_fst.comp measurable_snd)).prodMk
      (measurable_pi_lambda _ (fun t => measurable_hatEmp M hM t))
  have e1 : P.map (fun ω => (A ω, (Bξ ω, R ω))) = (P.map A).prod ((P.map Bξ).prod (P.map R)) := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hAm.aemeasurable (hBm.prodMk hRm).aemeasurable).1 h3.1,
      (indepFun_iff_map_prod_eq_prod_map_map hBm.aemeasurable hRm.aemeasurable).1 h3.2]
  have eA : P.map A = ((m.toPM : ProbabilityMeasure X) : Measure X) := by
    rw [hA, show (fun ω : NOmega T N X Γ => ω.1 0) = (fun x : Fin N → X => x 0) ∘ Prod.fst from rfl,
      ← Measure.map_map (measurable_pi_apply 0) measurable_fst, hP]
    unfold nLaw
    rw [Measure.map_fst_prod]
    simp only [measure_univ, one_smul, prodInit, ProbabilityMeasure.coe_mk]
    exact (measurePreserving_eval (fun _ : Fin N => ((m.toPM : ProbabilityMeasure X) : Measure X)) 0).map_eq
  have eB : P.map Bξ = Measure.pi fun _ : Fin T => (volume : Measure I) := by
    have hξ0 : Measurable (fun ξ : Fin T → Fin N → I => fun t => ξ t 0) :=
      measurable_pi_lambda _ (fun t => (measurable_pi_apply 0).comp (measurable_pi_apply t))
    rw [hBξ, show (fun ω : NOmega T N X Γ => fun t => ω.2.2 t 0) =
        (fun ξ : Fin T → Fin N → I => fun t => ξ t 0) ∘ Prod.snd ∘ Prod.snd from rfl,
      ← Measure.map_map hξ0 (measurable_snd.comp measurable_snd),
      ← Measure.map_map measurable_snd measurable_snd, hP]
    unfold nLaw
    rw [Measure.map_snd_prod]
    simp only [measure_univ, one_smul]
    rw [Measure.map_snd_prod]
    simp only [measure_univ, one_smul]
    rw [Measure.pi_map_pi (fun _ => (measurable_pi_apply 0).aemeasurable)]
    congr 1
    funext t
    exact (measurePreserving_eval (fun _ : Fin N => (volume : Measure I)) 0).map_eq
  have eR : P.map R = (rhoHat M hM (prodInit N m) γ : Measure (Strat T X Γ × Flow T X)) := rfl
  have hΘ : Θ M = (Prod.map id Prod.swap) ∘ (fun ω => (A ω, (Bξ ω, R ω))) := rfl
  rw [hΘ, ← Measure.map_map (measurable_id.prodMap measurable_swap) (hAm.prodMk (hBm.prodMk hRm)), e1,
    ← Measure.map_prod_map _ _ measurable_id measurable_swap, Measure.map_id, Measure.prod_swap,
    eA, eB, eR]
  rfl

end E

section F
variable {T : ℕ} {X Γ : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    [MeasurableSpace X] [DiscreteMeasurableSpace X]
    [Fintype Γ] [MeasurableSpace Γ] [DiscreteMeasurableSpace Γ]
    [TopologicalSpace Γ] [DiscreteTopology Γ]

lemma iterFin_go_congr' {S : Type} (s₀ : S) (step step' : Fin T → S → S) (τ : Fin T)
    (h : ∀ t : Fin T, t.val < τ.val → step t = step' t) :
    ∀ k, k ≤ τ.val → iterFin.go s₀ step k = iterFin.go s₀ step' k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    have hkT : k < T := by have := τ.isLt; omega
    simp only [iterFin.go, dif_pos hkT]
    rw [ih (by omega), h ⟨k, hkT⟩ (by simp; omega)]

/-- Player 1's state in the decoupled system: the mean field dynamics driven by
`(X_1(0), Φ_1, μ̂_1(·), ξ_1(·))` and the strategy modification `u`. -/
noncomputable def checkPath (M : Model T X Γ) (u : Strat T X Γ → Strat T X Γ) {N : ℕ} [NeZero N]
    (ω : NOmega T N X Γ) : Fin (T + 1) → X :=
  mfgPath M u (Θ M ω)

lemma measurable_checkPath (M : Model T X Γ) (hM : M.Standing) (u : Strat T X Γ → Strat T X Γ)
    {N : ℕ} [NeZero N] (t : Fin (T + 1)) :
    Measurable (fun ω : NOmega T N X Γ => checkPath M u ω t) :=
  (measurable_mfgPath M hM u t).comp (measurable_Θ M hM)

lemma checkPath_noise_congr (M : Model T X Γ) (u : Strat T X Γ → Strat T X Γ) {N : ℕ} [NeZero N]
    (ω ω' : NOmega T N X Γ) (h1 : ω.1 = ω'.1) (h2 : ω.2.1 = ω'.2.1) (τ : Fin T)
    (h3 : ∀ s, s ≠ τ → ω.2.2 s = ω'.2.2 s) (t : Fin (T + 1)) (ht : t.val ≤ τ.val) :
    checkPath M u ω t = checkPath M u ω' t := by
  unfold checkPath mfgPath iterFin Θ
  simp only
  rw [h1]
  apply iterFin_go_congr' _ _ _ τ _ t.val ht
  intro s hs
  have hne : s ≠ τ := by intro he; rw [he] at hs; exact lt_irrefl _ hs
  have hh : hatEmp M ω s.castSucc = hatEmp M ω' s.castSucc := by
    unfold hatEmp
    rw [hatPath_noise_congr M ω ω' h1 h2 τ h3 s.castSucc (by simp; omega)]
  funext x
  rw [hh, h2, h3 s hne]

lemma checkPath_succ (M : Model T X Γ) (u : Strat T X Γ → Strat T X Γ) {N : ℕ} [NeZero N]
    (ω : NOmega T N X Γ) (k : ℕ) (hk : k < T) :
    checkPath M u ω ⟨k + 1, Nat.succ_lt_succ hk⟩ =
      M.Ψ ⟨k, hk⟩ (checkPath M u ω ⟨k, Nat.lt_succ_of_lt hk⟩) (hatEmp M ω ⟨k, Nat.lt_succ_of_lt hk⟩)
        (u (ω.2.1 0) ⟨k, hk⟩ (checkPath M u ω ⟨k, Nat.lt_succ_of_lt hk⟩)) (ω.2.2 ⟨k, hk⟩ 0) := by
  unfold checkPath mfgPath
  rw [iterFin_succ _ _ k hk]
  rfl

lemma step_bound0 (M : Model T X Γ) (hM : M.Standing)
    (u : Strat T X Γ → Strat T X Γ) {N : ℕ} [NeZero N]
    (mN : ProbabilityMeasure (Fin N → X)) (γ : ProbabilityMeasure (Fin N → Strat T X Γ))
    (k : ℕ) (hk : k < T) (δ' δ : ℝ) (hδ : 0 < δ) (hδ' : 0 ≤ δ')
    (hψ : ∀ (τ : Fin T) (x : X) (a : Γ) (m m' : Meas X),
      (volume : Measure I) {z | M.Ψ τ x m a z ≠ M.Ψ τ x m' a z} ≤
        ENNReal.ofReal (δ' + distTV m m' / δ)) :
    (nLaw mN γ).real {ω | nPath M 0 u ω ⟨k + 1, Nat.succ_lt_succ hk⟩ 0 ≠
        checkPath M u ω ⟨k + 1, Nat.succ_lt_succ hk⟩} ≤
      (nLaw mN γ).real {ω | nPath M 0 u ω ⟨k, Nat.lt_succ_of_lt hk⟩ 0 ≠
        checkPath M u ω ⟨k, Nat.lt_succ_of_lt hk⟩} + δ' +
      (∫ ω, distTV (hatEmp M ω ⟨k, Nat.lt_succ_of_lt hk⟩)
        (tildeEmp M u ω 0 ⟨k, Nat.lt_succ_of_lt hk⟩) ∂(nLaw mN γ)) / δ := by
  set P := nLaw mN γ with hPdef
  set tk : Fin (T + 1) := ⟨k, Nat.lt_succ_of_lt hk⟩ with htk
  set τ : Fin T := ⟨k, hk⟩ with hτ
  set F : (Fin N → Strat T X Γ) × (Fin N → X) × (Fin N → X) × X → X × Meas X × Meas X × Γ :=
    fun q => (q.2.2.2, empOthers q.2.1 0, empOthers q.2.2.1 0, u (q.1 0) τ q.2.2.2) with hF
  set G : NOmega T N X Γ → X × Meas X × Meas X × Γ :=
    fun ω => F (ω.2.1, hatPath M ω tk, tildePath M u ω tk, checkPath M u ω tk) with hG
  have hGm : Measurable G := by
    refine (measurable_of_countable F).comp ?_
    exact (measurable_fst.comp measurable_snd).prodMk
      ((measurable_hatPath M hM tk).prodMk ((measurable_nPath M hM 0 u tk).prodMk
        (measurable_checkPath M hM u tk)))
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
  have hξm : Measurable (fun ω : NOmega T N X Γ => ω.2.2 τ 0) :=
    (measurable_pi_apply 0).comp ((measurable_pi_apply τ).comp (measurable_snd.comp measurable_snd))
  have hind : IndepFun G (fun ω => ω.2.2 τ 0) P := by
    have hI0 := indepFun_pi_at_rest (fun _ : Fin T => Measure.pi fun _ : Fin N => (volume : Measure I)) τ
    have hI1 := hI0.comp (measurable_pi_apply 0) measurable_id
    have hrest : Measurable (fun (ξ : Fin T → Fin N → I) (s : ↥(Finset.univ.erase τ)) => ξ s) :=
      measurable_pi_lambda _ (fun s => measurable_pi_apply _)
    have hB1 := indepFun_prod_right (μ := (γ : Measure (Fin N → Strat T X Γ)))
      ((measurable_pi_apply 0).comp (measurable_pi_apply τ)) (measurable_id.comp hrest) hI1
    have hB2 := indepFun_prod_right (μ := (mN : Measure (Fin N → X)))
      (((measurable_pi_apply 0).comp (measurable_pi_apply τ)).comp measurable_snd)
      (measurable_fst.prodMk ((measurable_id.comp hrest).comp measurable_snd)) hB1
    set Gf : (Fin N → X) × ((Fin N → Strat T X Γ) × (↥(Finset.univ.erase τ) → Fin N → I)) →
        X × Meas X × Meas X × Γ :=
      fun q => G (q.1, q.2.1, extAt τ (fun _ => (0 : I)) q.2.2) with hGf
    have hGfm : Measurable Gf := hGm.comp (measurable_fst.prodMk
      ((measurable_fst.comp measurable_snd).prodMk ((measurable_extAt τ _).comp
        (measurable_snd.comp measurable_snd))))
    have h := hB2.comp measurable_id hGfm
    have h' : IndepFun (fun ω : NOmega T N X Γ => ω.2.2 τ 0) G P := by
      refine h.congr (ae_of_all _ (fun ω => rfl)) (ae_of_all _ (fun ω => ?_))
      have hω : ∀ s, s ≠ τ → (extAt τ (fun _ => (0 : I))
          (fun s : ↥(Finset.univ.erase τ) => ω.2.2 s)) s = ω.2.2 s :=
        fun s hs => extAt_ne τ _ ω.2.2 s hs
      set ω' : NOmega T N X Γ := (ω.1, ω.2.1, extAt τ (fun _ => (0 : I))
          (fun s : ↥(Finset.univ.erase τ) => ω.2.2 s)) with hω'
      simp only [Function.comp_apply, id, hGf, hG]
      rw [show hatPath M ω' tk = hatPath M ω tk from
          hatPath_noise_congr M ω' ω rfl rfl τ hω tk le_rfl,
        show tildePath M u ω' tk = tildePath M u ω tk from
          nPath_noise_congr M 0 u ω' ω rfl rfl τ hω tk le_rfl,
        show checkPath M u ω' tk = checkPath M u ω tk from
          checkPath_noise_congr M u ω' ω rfl rfl τ hω tk le_rfl]
    exact h'.symm
  have hsub : {ω : NOmega T N X Γ | nPath M 0 u ω ⟨k + 1, Nat.succ_lt_succ hk⟩ 0 ≠
        checkPath M u ω ⟨k + 1, Nat.succ_lt_succ hk⟩} ⊆
      {ω | nPath M 0 u ω tk 0 ≠ checkPath M u ω tk} ∪ {ω | (G ω, ω.2.2 τ 0) ∈ S} := by
    intro ω hω
    by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
    obtain ⟨h1, h2⟩ := hc
    apply hω
    rw [checkPath_succ M u ω k hk]
    have hn : nPath M 0 u ω ⟨k + 1, Nat.succ_lt_succ hk⟩ 0 =
        M.Ψ τ (nPath M 0 u ω tk 0) (empOthers (nPath M 0 u ω tk) 0)
          (played 0 u ω.2.1 0 τ (nPath M 0 u ω tk 0)) (ω.2.2 τ 0) := by
      unfold nPath
      rw [iterFin_succ _ _ k hk]
    have hpl : played 0 u ω.2.1 0 = u (ω.2.1 0) := by simp [played]
    rw [hn, hpl, h1]
    simp only [hS, Set.mem_setOf_eq, not_not, hG, hF] at h2
    exact h2.symm
  have hS'm : MeasurableSet {ω | (G ω, ω.2.2 τ 0) ∈ S} := (hGm.prodMk hξm) hSm
  set D : NOmega T N X Γ → ℝ := fun ω => distTV (hatEmp M ω tk) (tildeEmp M u ω 0 tk) with hD
  have hDm : Measurable D := by
    have : D = (fun q : (Fin N → X) × (Fin N → X) => distTV (empOthers q.1 0) (empOthers q.2 0)) ∘
        (fun ω => (hatPath M ω tk, tildePath M u ω tk)) := rfl
    rw [this]
    exact (measurable_of_countable _).comp ((measurable_hatPath M hM tk).prodMk
      (measurable_nPath M hM 0 u tk))
  have hDint : Integrable D P :=
    Integrable.of_bound hDm.aestronglyMeasurable 1 (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (distTV_nonneg _ _)]; exact distTV_le_one _ _)
  have hfint : Integrable (fun ω => δ' + D ω / δ) P :=
    (integrable_const δ').add (hDint.div_const δ)
  have hS'bound : P {ω | (G ω, ω.2.2 τ 0) ∈ S} ≤ ∫⁻ ω, ENNReal.ofReal (δ' + D ω / δ) ∂P := by
    rw [prob_section_eq hξm (nLaw_map_noise mN γ τ 0) hGm hind hSm]
    refine lintegral_mono fun ω => ?_
    exact hψ τ _ _ _ _
  have hS'real : P.real {ω | (G ω, ω.2.2 τ 0) ∈ S} ≤ δ' + (∫ ω, D ω ∂P) / δ := by
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
  calc P.real _ ≤ P.real ({ω | nPath M 0 u ω tk 0 ≠ checkPath M u ω tk} ∪
          {ω | (G ω, ω.2.2 τ 0) ∈ S}) := measureReal_mono hsub
    _ ≤ P.real {ω | nPath M 0 u ω tk 0 ≠ checkPath M u ω tk} +
          P.real {ω | (G ω, ω.2.2 τ 0) ∈ S} := measureReal_union_le _ _
    _ ≤ _ := by rw [add_assoc]; gcongr

end F

section G
variable {T : ℕ} {X Γ : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    [TopologicalSpace X] [DiscreteTopology X]
    [MeasurableSpace X] [DiscreteMeasurableSpace X]
    [Fintype Γ] [Nonempty Γ] [MeasurableSpace Γ] [DiscreteMeasurableSpace Γ]
    [TopologicalSpace Γ] [DiscreteTopology Γ]

/-- Player 1's actual state and its decoupled counterpart agree with probability tending to one. -/
lemma coupling0 (M : Model T X Γ) (hM : M.Standing) (hA1a : M.A1a) (u : Strat T X Γ → Strat T X Γ)
    (mN : (n : ℕ) → ProbabilityMeasure (Fin (n + 2) → X))
    (γ : (n : ℕ) → ProbabilityMeasure (Fin (n + 2) → Strat T X Γ)) (t : Fin (T + 1)) :
    Tendsto (fun n : ℕ => (nLaw (mN n) (γ n)).real
      {ω | nPath M 0 u ω t 0 ≠ checkPath M u ω t}) atTop (𝓝 0) := by
  set b : ℕ → Fin (T + 1) → ℝ := fun n t => (nLaw (mN n) (γ n)).real
      {ω | nPath M 0 u ω t 0 ≠ checkPath M u ω t} with hb
  have hb0 : ∀ n t, 0 ≤ b n t := fun n t => measureReal_nonneg
  suffices key : ∀ k (hk : k < T + 1), Tendsto (fun n => b n ⟨k, hk⟩) atTop (𝓝 0) from
    key t.val t.isLt
  intro k
  induction k with
  | zero =>
    intro hk
    have : ∀ n, b n ⟨0, hk⟩ = 0 := by
      intro n
      simp only [hb]
      have : {ω : NOmega T (n + 2) X Γ | nPath M 0 u ω ⟨0, hk⟩ 0 ≠ checkPath M u ω ⟨0, hk⟩} = ∅ := by
        ext ω; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]; rfl
      rw [this, measureReal_empty]
    simp_rw [this]
    exact tendsto_const_nhds
  | succ k ih =>
    intro hk
    have hkT : k < T := by omega
    have ih' := ih (Nat.lt_succ_of_lt hkT)
    have ha := eq_6_2 M hM hA1a u mN γ ⟨k, Nat.lt_succ_of_lt hkT⟩
    have hc : Tendsto (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      simpa using this
    set a : ℕ → ℝ := fun n => (1 / ((n + 1 : ℕ) : ℝ)) *
        ∑ j ∈ Finset.univ.erase (0 : Fin (n + 2)),
          (nLaw (mN n) (γ n)).real {ω | hatPath M ω ⟨k, Nat.lt_succ_of_lt hkT⟩ j ≠
            tildePath M u ω ⟨k, Nat.lt_succ_of_lt hkT⟩ j} with hadef
    have ha0 : ∀ n, 0 ≤ a n := fun n =>
      mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => measureReal_nonneg)
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨δ, hδ, hψ⟩ := psi_bound M hA1a (ε / 2) (by positivity)
    have hrec : ∀ n, b n ⟨k + 1, hk⟩ ≤ b n ⟨k, Nat.lt_succ_of_lt hkT⟩ + ε / 2 +
        (1 / ((n + 1 : ℕ) : ℝ) + a n) / δ := by
      intro n
      have hN : 2 ≤ n + 2 := by omega
      have h1 := step_bound0 M hM u (mN n) (γ n) k hkT (ε / 2) δ hδ (by positivity) hψ
      have h2 := eq_6_3 M hM u hN (mN n) (γ n) 0 ⟨k, Nat.lt_succ_of_lt hkT⟩
      have hNsub : ((n + 2 - 1 : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) := by congr 1
      rw [hNsub] at h2
      refine h1.trans ?_
      gcongr
    have hlim : Tendsto (fun n => b n ⟨k, Nat.lt_succ_of_lt hkT⟩ +
        (1 / ((n + 1 : ℕ) : ℝ) + a n) / δ) atTop (𝓝 0) := by
      have := ih'.add ((hc.add ha).div_const δ)
      simpa using this
    obtain ⟨N0, hN0⟩ := (Metric.tendsto_atTop.mp hlim) (ε / 2) (by positivity)
    refine ⟨N0, fun n hn => ?_⟩
    have h1 := hN0 n hn
    rw [Real.dist_eq, sub_zero] at h1 ⊢
    have h2 := hrec n
    have h3 := hb0 n ⟨k + 1, hk⟩
    have h4 := hb0 n ⟨k, Nat.lt_succ_of_lt hkT⟩
    rw [abs_of_nonneg h3]
    have h6 : (0 : ℝ) ≤ 1 / ((n + 1 : ℕ) : ℝ) := by positivity
    have h5 : 0 ≤ (1 / ((n + 1 : ℕ) : ℝ) + a n) / δ := div_nonneg (add_nonneg h6 (ha0 n)) hδ.le
    have h7 : 0 ≤ b n ⟨k, Nat.lt_succ_of_lt hkT⟩ + (1 / ((n + 1 : ℕ) : ℝ) + a n) / δ :=
      add_nonneg h4 h5
    rw [abs_of_nonneg h7] at h1
    linarith

end G

section H
variable {T : ℕ} {X Γ : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    [TopologicalSpace X] [DiscreteTopology X]
    [MeasurableSpace X] [DiscreteMeasurableSpace X]
    [Fintype Γ] [Nonempty Γ] [MeasurableSpace Γ] [DiscreteMeasurableSpace Γ]
    [TopologicalSpace Γ] [DiscreteTopology Γ]

lemma distTV_comm' (m m' : Meas X) : distTV m m' = distTV m' m := by
  unfold distTV
  congr 1
  exact Finset.sum_congr rfl fun x _ => abs_sub_comm _ _

lemma VQ_rhoHat_eq (M : Model T X Γ) (hM : M.Standing) (u : Strat T X Γ → Strat T X Γ)
    (G : GoodQ T X Γ) {N : ℕ} [NeZero N] (hN : 2 ≤ N) (m : Meas X)
    (γ : ProbabilityMeasure (Fin N → Strat T X Γ)) :
    VQ M u G m (rhoHat M hM (prodInit N m) γ) =
      ∫ ω, G.Q (checkPath M u ω) (ω.2.1 0) (fun t => hatEmp M ω t) ∂(nLaw (prodInit N m) γ) := by
  unfold VQ
  rw [← nLaw_map_Θ M hM hN m γ, integral_map (measurable_Θ M hM).aemeasurable
    (measurable_Qpath M hM u G).aestronglyMeasurable]
  rfl

lemma measurable_tildeFlow (M : Model T X Γ) (hM : M.Standing) (u : Strat T X Γ → Strat T X Γ)
    {N : ℕ} [NeZero N] :
    Measurable (fun ω : NOmega T N X Γ => fun t => empOthers (nPath M 0 u ω t) 0) :=
  measurable_pi_lambda _ (fun t => (measurable_of_countable (fun x : Fin N → X => empOthers x 0)).comp
    (measurable_nPath M hM 0 u t))

lemma measurable_hatFlow (M : Model T X Γ) (hM : M.Standing) {N : ℕ} [NeZero N] :
    Measurable (fun ω : NOmega T N X Γ => fun t => hatEmp M ω t) :=
  measurable_pi_lambda _ (fun t => measurable_hatEmp M hM t)

/-- Claim A: the expectation of `Q` along player 1's actual data and along the decoupled data
have the same limit. -/
lemma claimA (M : Model T X Γ) (hM : M.Standing) (hA1a : M.A1a) (u : Strat T X Γ → Strat T X Γ)
    (G : GoodQ T X Γ) (m0N : ℕ → Meas X) (γ : (N : ℕ) → ProbabilityMeasure (Fin N → Strat T X Γ)) :
    Tendsto (fun n : ℕ =>
      (∫ ω, G.Q (fun t => nPath M 0 u ω t 0) (ω.2.1 0) (fun t => empOthers (nPath M 0 u ω t) 0)
          ∂(nLaw (prodInit (n + 2) (m0N (n + 2))) (γ (n + 2)))) -
        VQ M u G (m0N (n + 2)) (rhoHat M hM (prodInit (n + 2) (m0N (n + 2))) (γ (n + 2))))
      atTop (𝓝 0) := by
  set mN : (n : ℕ) → ProbabilityMeasure (Fin (n + 2) → X) := fun n => prodInit (n + 2) (m0N (n + 2))
  set γN : (n : ℕ) → ProbabilityMeasure (Fin (n + 2) → Strat T X Γ) := fun n => γ (n + 2)
  have hcoup : ∀ t, Tendsto (fun n : ℕ => (nLaw (mN n) (γN n)).real
      {ω | nPath M 0 u ω t 0 ≠ checkPath M u ω t}) atTop (𝓝 0) :=
    fun t => coupling0 M hM hA1a u mN γN t
  have hR : Tendsto (fun n : ℕ => ∑ t, (nLaw (mN n) (γN n)).real
      {ω | nPath M 0 u ω t 0 ≠ checkPath M u ω t}) atTop (𝓝 0) := by
    have := tendsto_finset_sum (Finset.univ : Finset (Fin (T + 1))) (fun t _ => hcoup t)
    simpa using this
  have hc : Tendsto (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa using this
  set a : ℕ → Fin (T + 1) → ℝ := fun n t => (1 / ((n + 1 : ℕ) : ℝ)) *
      ∑ j ∈ Finset.univ.erase (0 : Fin (n + 2)),
        (nLaw (mN n) (γN n)).real {ω | hatPath M ω t j ≠ tildePath M u ω t j} with hadef
  have hD : Tendsto (fun n : ℕ => ∑ t, (1 / ((n + 1 : ℕ) : ℝ) + a n t)) atTop (𝓝 0) := by
    have := tendsto_finset_sum (Finset.univ : Finset (Fin (T + 1)))
      (fun t _ => hc.add (eq_6_2 M hM hA1a u mN γN t))
    simpa only [add_zero, Finset.sum_const_zero] using this
  have hED : ∀ n t, ∫ ω, distTV (empOthers (nPath M 0 u ω t) 0) (hatEmp M ω t) ∂(nLaw (mN n) (γN n))
      ≤ 1 / ((n + 1 : ℕ) : ℝ) + a n t := by
    intro n t
    have hN : 2 ≤ n + 2 := by omega
    have h2 := eq_6_3 M hM u hN (mN n) (γN n) 0 t
    have hNsub : ((n + 2 - 1 : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) := by congr 1
    rw [hNsub] at h2
    have : ∀ ω : NOmega T (n + 2) X Γ, distTV (empOthers (nPath M 0 u ω t) 0) (hatEmp M ω t) =
        distTV (hatEmp M ω t) (tildeEmp M u ω 0 t) := fun ω => distTV_comm' _ _
    simp_rw [this]
    exact h2
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hu⟩ := unif_family (fun i : (Fin (T + 1) → X) × Strat T X Γ => G.Q i.1 i.2)
    (fun i => G.cont i.1 i.2) (ε / 2) (by positivity)
  have hC := G.C_nonneg
  have hlim : Tendsto (fun n : ℕ => 4 * G.C / δ * ∑ t, (1 / ((n + 1 : ℕ) : ℝ) + a n t) +
      2 * G.C * ∑ t, (nLaw (mN n) (γN n)).real {ω | nPath M 0 u ω t 0 ≠ checkPath M u ω t})
      atTop (𝓝 0) := by
    have := (hD.const_mul (4 * G.C / δ)).add (hR.const_mul (2 * G.C))
    simpa using this
  obtain ⟨N0, hN0⟩ := Metric.tendsto_atTop.mp hlim (ε / 2) (by positivity)
  refine ⟨N0, fun n hn => ?_⟩
  have hN : 2 ≤ n + 2 := by omega
  have hbound := hN0 n hn
  rw [Real.dist_eq, sub_zero] at hbound ⊢
  set P := nLaw (mN n) (γN n) with hP
  -- the two integrands
  set A : NOmega T (n + 2) X Γ → ℝ := fun ω =>
    G.Q (fun t => nPath M 0 u ω t 0) (ω.2.1 0) (fun t => empOthers (nPath M 0 u ω t) 0) with hA
  set B : NOmega T (n + 2) X Γ → ℝ := fun ω =>
    G.Q (checkPath M u ω) (ω.2.1 0) (fun t => hatEmp M ω t) with hB
  have hpath : Measurable (fun ω : NOmega T (n + 2) X Γ => fun t => nPath M 0 u ω t 0) :=
    measurable_pi_lambda _ (fun t => (measurable_pi_apply 0).comp (measurable_nPath M hM 0 u t))
  have hφ : Measurable (fun ω : NOmega T (n + 2) X Γ => ω.2.1 0) :=
    (measurable_pi_apply 0).comp (measurable_fst.comp measurable_snd)
  have hAm : Measurable A :=
    G.measurable.comp ((hpath.prodMk hφ).prodMk (measurable_tildeFlow M hM u))
  have hBm : Measurable B :=
    G.measurable.comp (((measurable_pi_lambda _ (fun t => measurable_checkPath M hM u t)).prodMk hφ).prodMk
      (measurable_hatFlow M hM))
  have hAi : Integrable A P := Integrable.of_bound hAm.aestronglyMeasurable G.C
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact G.bound _ _ _)
  have hBi : Integrable B P := Integrable.of_bound hBm.aestronglyMeasurable G.C
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact G.bound _ _ _)
  -- the error terms
  set E : Fin (T + 1) → Set (NOmega T (n + 2) X Γ) :=
    fun t => {ω | nPath M 0 u ω t 0 ≠ checkPath M u ω t} with hE
  have hEm : ∀ t, MeasurableSet (E t) := fun t =>
    (measurableSet_eq_fun ((measurable_pi_apply 0).comp (measurable_nPath M hM 0 u t))
      (measurable_checkPath M hM u t)).compl
  set Dd : Fin (T + 1) → NOmega T (n + 2) X Γ → ℝ :=
    fun t ω => distTV (empOthers (nPath M 0 u ω t) 0) (hatEmp M ω t) with hDd
  have hDdm : ∀ t, Measurable (Dd t) := by
    intro t
    have : Dd t = (fun q : (Fin (n + 2) → X) × (Fin (n + 2) → X) =>
        distTV (empOthers q.1 0) (empOthers q.2 0)) ∘
        (fun ω => (nPath M 0 u ω t, hatPath M ω t)) := rfl
    rw [this]
    exact (measurable_of_countable _).comp ((measurable_nPath M hM 0 u t).prodMk
      (measurable_hatPath M hM t))
  have hDdi : ∀ t, Integrable (Dd t) P := fun t =>
    Integrable.of_bound (hDdm t).aestronglyMeasurable 1 (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (distTV_nonneg _ _)]; exact distTV_le_one _ _)
  have hIi : ∀ t, Integrable ((E t).indicator (fun _ => (1 : ℝ))) P :=
    fun t => (integrable_const _).indicator (hEm t)
  set RHS : NOmega T (n + 2) X Γ → ℝ := fun ω => ε / 2 + 4 * G.C / δ * ∑ t, Dd t ω +
    2 * G.C * ∑ t, (E t).indicator (fun _ => (1 : ℝ)) ω with hRHS
  have hRHSi : Integrable RHS P :=
    (((integrable_const _).add ((integrable_finset_sum _ fun t _ => hDdi t).const_mul _)).add
      ((integrable_finset_sum _ fun t _ => hIi t).const_mul _) : _)
  have hpt : ∀ ω, |A ω - B ω| ≤ RHS ω := by
    intro ω
    set A' := G.Q (fun t => nPath M 0 u ω t 0) (ω.2.1 0) (fun t => hatEmp M ω t)
    have h1 : |A ω - A'| ≤ ε / 2 + 2 * G.C * (2 * ∑ t, Dd t ω) / δ :=
      unif_bound (fun i : (Fin (T + 1) → X) × Strat T X Γ => G.Q i.1 i.2) G.C
        (fun i μ => G.bound i.1 i.2 μ) (ε / 2) δ hδ hu ((fun t => nPath M 0 u ω t 0), ω.2.1 0)
        (fun t => empOthers (nPath M 0 u ω t) 0) (fun t => hatEmp M ω t)
    have hInn : 0 ≤ ∑ t, (E t).indicator (fun _ => (1 : ℝ)) ω :=
      Finset.sum_nonneg fun t _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _
    have h2 : |A' - B ω| ≤ 2 * G.C * ∑ t, (E t).indicator (fun _ => (1 : ℝ)) ω := by
      by_cases hall : ∀ t, nPath M 0 u ω t 0 = checkPath M u ω t
      · have : (fun t => nPath M 0 u ω t 0) = checkPath M u ω := funext hall
        simp only [A', hB, this, sub_self, abs_zero]
        positivity
      · push_neg at hall
        obtain ⟨t0, ht0⟩ := hall
        have h1 : (1 : ℝ) ≤ ∑ t, (E t).indicator (fun _ => (1 : ℝ)) ω := by
          have := Finset.single_le_sum (f := fun t => (E t).indicator (fun _ => (1 : ℝ)) ω)
            (fun t _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _) (Finset.mem_univ t0)
          rw [Set.indicator_of_mem (show ω ∈ E t0 from ht0)] at this
          exact this
        have h3 : |A' - B ω| ≤ 2 * G.C := by
          have := abs_sub A' (B ω); have := G.bound (fun t => nPath M 0 u ω t 0) (ω.2.1 0)
            (fun t => hatEmp M ω t)
          have := G.bound (checkPath M u ω) (ω.2.1 0) (fun t => hatEmp M ω t)
          simp only [A', hB] at *
          linarith
        nlinarith
    have h3 := abs_sub_le (A ω) A' (B ω)
    have : 2 * G.C * (2 * ∑ t, Dd t ω) / δ = 4 * G.C / δ * ∑ t, Dd t ω := by ring
    simp only [hRHS]
    linarith
  have hint : |∫ ω, A ω ∂P - ∫ ω, B ω ∂P| ≤ ∫ ω, RHS ω ∂P := by
    rw [← integral_sub hAi hBi]
    refine (abs_integral_le_integral_abs).trans ?_
    exact integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) hRHSi (ae_of_all _ hpt)
  have hI1 : Integrable (fun ω => 4 * G.C / δ * ∑ t, Dd t ω) P :=
    (integrable_finset_sum _ fun t _ => hDdi t).const_mul _
  have hI2 : Integrable (fun ω => 2 * G.C * ∑ t, (E t).indicator (fun _ => (1 : ℝ)) ω) P :=
    (integrable_finset_sum _ fun t _ => hIi t).const_mul _
  have hI12 : Integrable (fun ω => ε / 2 + 4 * G.C / δ * ∑ t, Dd t ω) P :=
    (integrable_const _).add hI1
  have hRHSv : ∫ ω, RHS ω ∂P = ε / 2 + 4 * G.C / δ * ∑ t, ∫ ω, Dd t ω ∂P +
      2 * G.C * ∑ t, P.real (E t) := by
    simp only [hRHS]
    rw [integral_add hI12 hI2, integral_add (integrable_const _) hI1,
      integral_const_mul, integral_const_mul, integral_finset_sum _ fun t _ => hDdi t,
      integral_finset_sum _ fun t _ => hIi t]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    congr 2
    exact Finset.sum_congr rfl fun t _ => by rw [integral_indicator (hEm t), setIntegral_const]; simp
  have hED' : ∑ t, ∫ ω, Dd t ω ∂P ≤ ∑ t, (1 / ((n + 1 : ℕ) : ℝ) + a n t) :=
    Finset.sum_le_sum fun t _ => hED n t
  rw [VQ_rhoHat_eq M hM u G hN (m0N (n + 2)) (γ (n + 2))]
  have habs : 0 ≤ 4 * G.C / δ * ∑ t, (1 / ((n + 1 : ℕ) : ℝ) + a n t) +
      2 * G.C * ∑ t, (nLaw (mN n) (γN n)).real {ω | nPath M 0 u ω t 0 ≠ checkPath M u ω t} := by
    have : 0 ≤ ∑ t, ∫ ω, Dd t ω ∂P := Finset.sum_nonneg fun t _ =>
      integral_nonneg fun ω => distTV_nonneg _ _
    have : 0 ≤ ∑ t, P.real (E t) := Finset.sum_nonneg fun t _ => measureReal_nonneg
    have : 0 ≤ 4 * G.C / δ := by positivity
    nlinarith
  rw [abs_of_nonneg habs] at hbound
  have h4 : 4 * G.C / δ * ∑ t, ∫ ω, Dd t ω ∂P ≤ 4 * G.C / δ * ∑ t, (1 / ((n + 1 : ℕ) : ℝ) + a n t) := by
    gcongr
  change |∫ ω, A ω ∂P - ∫ ω, B ω ∂P| < ε
  have : ∑ t, P.real (E t) = ∑ t, (nLaw (mN n) (γN n)).real
      {ω | nPath M 0 u ω t 0 ≠ checkPath M u ω t} := rfl
  linarith

lemma meas_sum_one (m : Meas X) : ∑ x, (m : X → ℝ) x = 1 := m.2.2

/-- Claim B: replacing the law `ρ^N` of `(Φ_1, μ_1(·))` by the law of `(Φ_1, μ̂_1(·))` does not change
the limit of `V`. -/
lemma claimB (M : Model T X Γ) (hM : M.Standing) (hA1a : M.A1a) (u : Strat T X Γ → Strat T X Γ)
    (G : GoodQ T X Γ) (m0N : ℕ → Meas X) (γ : (N : ℕ) → ProbabilityMeasure (Fin N → Strat T X Γ)) :
    Tendsto (fun n : ℕ =>
      VQ M u G (m0N (n + 2)) (rhoHat M hM (prodInit (n + 2) (m0N (n + 2))) (γ (n + 2))) -
        VQ M u G (m0N (n + 2)) (rhoSeq M m0N γ n)) atTop (𝓝 0) := by
  set mN : (n : ℕ) → ProbabilityMeasure (Fin (n + 2) → X) := fun n => prodInit (n + 2) (m0N (n + 2))
  set γN : (n : ℕ) → ProbabilityMeasure (Fin (n + 2) → Strat T X Γ) := fun n => γ (n + 2)
  have hc : Tendsto (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa using this
  set a : ℕ → Fin (T + 1) → ℝ := fun n t => (1 / ((n + 1 : ℕ) : ℝ)) *
      ∑ j ∈ Finset.univ.erase (0 : Fin (n + 2)),
        (nLaw (mN n) (γN n)).real {ω | hatPath M ω t j ≠ tildePath M id ω t j} with hadef
  have hD : Tendsto (fun n : ℕ => ∑ t, (1 / ((n + 1 : ℕ) : ℝ) + a n t)) atTop (𝓝 0) := by
    have := tendsto_finset_sum (Finset.univ : Finset (Fin (T + 1)))
      (fun t _ => hc.add (eq_6_2 M hM hA1a id mN γN t))
    simpa only [add_zero, Finset.sum_const_zero] using this
  have hED : ∀ n t, ∫ ω, distTV (hatEmp M ω t) (empOthers (nPath M 0 id ω t) 0) ∂(nLaw (mN n) (γN n))
      ≤ 1 / ((n + 1 : ℕ) : ℝ) + a n t := by
    intro n t
    have hN : 2 ≤ n + 2 := by omega
    have h2 := eq_6_3 M hM id hN (mN n) (γN n) 0 t
    have hNsub : ((n + 2 - 1 : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) := by congr 1
    rw [hNsub] at h2
    exact h2
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hu⟩ := unif_family (fun i : X × Strat T X Γ => fun μ => HQ M u G i.1 (i.2, μ))
    (fun i => HQ_continuous_flow M hM hA1a u G i.1 i.2) (ε / 2) (by positivity)
  have hC := G.C_nonneg
  have hlim : Tendsto (fun n : ℕ => 4 * G.C / δ * ∑ t, (1 / ((n + 1 : ℕ) : ℝ) + a n t))
      atTop (𝓝 0) := by
    have := hD.const_mul (4 * G.C / δ)
    simpa using this
  obtain ⟨N0, hN0⟩ := Metric.tendsto_atTop.mp hlim (ε / 2) (by positivity)
  refine ⟨N0, fun n hn => ?_⟩
  have hbound := hN0 n hn
  rw [Real.dist_eq, sub_zero] at hbound ⊢
  set P := nLaw (mN n) (γN n) with hP
  set K : ℝ := ε / 2 + 4 * G.C / δ * ∑ t, (1 / ((n + 1 : ℕ) : ℝ) + a n t) with hK
  have hφ : Measurable (fun ω : NOmega T (n + 2) X Γ => ω.2.1 0) :=
    (measurable_pi_apply 0).comp (measurable_fst.comp measurable_snd)
  set Dd : Fin (T + 1) → NOmega T (n + 2) X Γ → ℝ :=
    fun t ω => distTV (hatEmp M ω t) (empOthers (nPath M 0 id ω t) 0) with hDd
  have hDdm : ∀ t, Measurable (Dd t) := by
    intro t
    have : Dd t = (fun q : (Fin (n + 2) → X) × (Fin (n + 2) → X) =>
        distTV (empOthers q.1 0) (empOthers q.2 0)) ∘
        (fun ω => (hatPath M ω t, nPath M 0 id ω t)) := rfl
    rw [this]
    exact (measurable_of_countable _).comp ((measurable_hatPath M hM t).prodMk
      (measurable_nPath M hM 0 id t))
  have hDdi : ∀ t, Integrable (Dd t) P := fun t =>
    Integrable.of_bound (hDdm t).aestronglyMeasurable 1 (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (distTV_nonneg _ _)]; exact distTV_le_one _ _)
  have hdiff : ∀ x₀ : X, |∫ q, HQ M u G x₀ q ∂(rhoHat M hM (mN n) (γN n) : Measure _) -
      ∫ q, HQ M u G x₀ q ∂(rhoSeq M m0N γ n : Measure _)| ≤ K := by
    intro x₀
    have hHm : Measurable (fun q : Strat T X Γ × Flow T X => HQ M u G x₀ q) :=
      (HQ_continuous M hM hA1a u G x₀).measurable
    have e1 : ∫ q, HQ M u G x₀ q ∂(rhoHat M hM (mN n) (γN n) : Measure _) =
        ∫ ω, HQ M u G x₀ (ω.2.1 0, fun t => hatEmp M ω t) ∂P := by
      show ∫ q, HQ M u G x₀ q ∂((nLaw (mN n) (γN n)).map
        (fun ω => (ω.2.1 0, fun t => hatEmp M ω t))) = _
      rw [integral_map (hφ.prodMk (measurable_hatFlow M hM)).aemeasurable hHm.aestronglyMeasurable]
    have e2 : ∫ q, HQ M u G x₀ q ∂(rhoSeq M m0N γ n : Measure _) =
        ∫ ω, HQ M u G x₀ (ω.2.1 0, fun t => empOthers (nPath M 0 id ω t) 0) ∂P := by
      show ∫ q, HQ M u G x₀ q ∂(rhoN M (mN n) (γN n) : Measure _) = _
      rw [rhoN_coe M hM, integral_map (measurable_rhoMap M hM).aemeasurable hHm.aestronglyMeasurable]
      rfl
    rw [e1, e2]
    have hA : Integrable (fun ω : NOmega T (n + 2) X Γ => HQ M u G x₀ (ω.2.1 0, fun t => hatEmp M ω t)) P :=
      Integrable.of_bound (hHm.comp (hφ.prodMk (measurable_hatFlow M hM))).aestronglyMeasurable G.C
        (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact HQ_abs_le M u G x₀ _)
    have hB : Integrable (fun ω : NOmega T (n + 2) X Γ =>
        HQ M u G x₀ (ω.2.1 0, fun t => empOthers (nPath M 0 id ω t) 0)) P :=
      Integrable.of_bound (hHm.comp (hφ.prodMk (measurable_tildeFlow M hM id))).aestronglyMeasurable G.C
        (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact HQ_abs_le M u G x₀ _)
    rw [← integral_sub hA hB]
    refine (abs_integral_le_integral_abs).trans ?_
    have hI1 : Integrable (fun ω => 4 * G.C / δ * ∑ t, Dd t ω) P :=
      (integrable_finset_sum _ fun t _ => hDdi t).const_mul _
    have hRi : Integrable (fun ω => ε / 2 + 4 * G.C / δ * ∑ t, Dd t ω) P :=
      (integrable_const _).add hI1
    have hpt : ∀ ω : NOmega T (n + 2) X Γ, |HQ M u G x₀ (ω.2.1 0, fun t => hatEmp M ω t) -
        HQ M u G x₀ (ω.2.1 0, fun t => empOthers (nPath M 0 id ω t) 0)| ≤
        ε / 2 + 4 * G.C / δ * ∑ t, Dd t ω := by
      intro ω
      have := unif_bound (fun i : X × Strat T X Γ => fun μ => HQ M u G i.1 (i.2, μ)) G.C
        (fun i μ => HQ_abs_le M u G i.1 _) (ε / 2) δ hδ hu (x₀, ω.2.1 0)
        (fun t => hatEmp M ω t) (fun t => empOthers (nPath M 0 id ω t) 0)
      have e : 2 * G.C * (2 * ∑ t, Dd t ω) / δ = 4 * G.C / δ * ∑ t, Dd t ω := by ring
      simp only at this
      linarith
    calc ∫ ω, |HQ M u G x₀ (ω.2.1 0, fun t => hatEmp M ω t) -
          HQ M u G x₀ (ω.2.1 0, fun t => empOthers (nPath M 0 id ω t) 0)| ∂P
        ≤ ∫ ω, (ε / 2 + 4 * G.C / δ * ∑ t, Dd t ω) ∂P :=
          integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) hRi (ae_of_all _ hpt)
      _ = ε / 2 + 4 * G.C / δ * ∑ t, ∫ ω, Dd t ω ∂P := by
          rw [integral_add (integrable_const _) hI1, integral_const_mul,
            integral_finset_sum _ fun t _ => hDdi t]
          simp
      _ ≤ K := by
          have : ∑ t, ∫ ω, Dd t ω ∂P ≤ ∑ t, (1 / ((n + 1 : ℕ) : ℝ) + a n t) :=
            Finset.sum_le_sum fun t _ => hED n t
          have : 0 ≤ 4 * G.C / δ := by positivity
          simp only [hK]
          nlinarith
  rw [VQ_eq_sum M hM u G, VQ_eq_sum M hM u G, ← Finset.sum_sub_distrib]
  have hm0 : ∀ x, 0 ≤ (m0N (n + 2) : X → ℝ) x := fun x => (m0N (n + 2)).2.1 x
  calc |∑ x, ((m0N (n + 2) : X → ℝ) x * ∫ q, HQ M u G x q ∂(rhoHat M hM (mN n) (γN n) : Measure _) -
        (m0N (n + 2) : X → ℝ) x * ∫ q, HQ M u G x q ∂(rhoSeq M m0N γ n : Measure _))|
      ≤ ∑ x, |(m0N (n + 2) : X → ℝ) x * ∫ q, HQ M u G x q ∂(rhoHat M hM (mN n) (γN n) : Measure _) -
        (m0N (n + 2) : X → ℝ) x * ∫ q, HQ M u G x q ∂(rhoSeq M m0N γ n : Measure _)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, (m0N (n + 2) : X → ℝ) x * K := by
        gcongr with x
        rw [← mul_sub, abs_mul, abs_of_nonneg (hm0 x)]
        exact mul_le_mul_of_nonneg_left (hdiff x) (hm0 x)
    _ = K := by rw [← Finset.sum_mul, meas_sum_one, one_mul]
    _ < ε := by
        have : 4 * G.C / δ * ∑ t, (1 / ((n + 1 : ℕ) : ℝ) + a n t) < ε / 2 := by
          have h0 : 0 ≤ 4 * G.C / δ * ∑ t, (1 / ((n + 1 : ℕ) : ℝ) + a n t) := by
            have : ∀ t, 0 ≤ a n t := fun t =>
              mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => measureReal_nonneg)
            have : 0 ≤ ∑ t, (1 / ((n + 1 : ℕ) : ℝ) + a n t) :=
              Finset.sum_nonneg fun t _ => add_nonneg (by positivity) (this t)
            positivity
          rwa [abs_of_nonneg h0] at hbound
        simp only [hK]
        linarith

end H

section SecOpt
variable {T : ℕ} {X Γ : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    [TopologicalSpace X] [DiscreteTopology X]
    [MeasurableSpace X] [DiscreteMeasurableSpace X]
    [Fintype Γ] [Nonempty Γ] [MeasurableSpace Γ] [DiscreteMeasurableSpace Γ]
    [TopologicalSpace Γ] [DiscreteTopology Γ]

/-- The cost functional as a test functional. -/
noncomputable def Qcost (M : Model T X Γ) (hM : M.Standing) (hA2 : M.A2)
    (u : Strat T X Γ → Strat T X Γ) : GoodQ T X Γ where
  Q p φ μ := (∑ t : Fin T, M.f t (p t.castSucc) (μ t.castSucc) (u φ t (p t.castSucc))) +
    M.F (p (Fin.last T)) (μ (Fin.last T))
  C := T * |Classical.choose hM.2.2.2| + |Classical.choose hM.2.2.2|
  C_nonneg := by positivity
  bound p φ μ := by
    have hC := Classical.choose_spec hM.2.2.2
    set C0 := Classical.choose hM.2.2.2
    have h1 : |∑ t : Fin T, M.f t (p t.castSucc) (μ t.castSucc) (u φ t (p t.castSucc))| ≤ T * |C0| := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have : ∀ t : Fin T, |M.f t (p t.castSucc) (μ t.castSucc) (u φ t (p t.castSucc))| ≤ |C0| :=
        fun t => (hC.1 _ _ _ _).trans (le_abs_self _)
      refine (Finset.sum_le_sum fun t _ => this t).trans ?_
      simp
    have h2 : |M.F (p (Fin.last T)) (μ (Fin.last T))| ≤ |C0| := (hC.2 _ _).trans (le_abs_self _)
    exact (abs_add_le _ _).trans (by linarith)
  cont p φ := by
    refine Continuous.add (continuous_finset_sum _ fun t _ => ?_) ?_
    · exact (hA2.1 t (p t.castSucc) (u φ t (p t.castSucc))).comp (continuous_apply t.castSucc)
    · exact (hA2.2 (p (Fin.last T))).comp (continuous_apply (Fin.last T))

lemma costN_eq_Qcost (M : Model T X Γ) (hM : M.Standing) (hA2 : M.A2) (u : Strat T X Γ → Strat T X Γ)
    {N : ℕ} [NeZero N] (mN : ProbabilityMeasure (Fin N → X))
    (γ : ProbabilityMeasure (Fin N → Strat T X Γ)) :
    costN M mN γ 0 u = ∫ ω, (Qcost M hM hA2 u).Q (fun t => nPath M 0 u ω t 0) (ω.2.1 0)
      (fun t => empOthers (nPath M 0 u ω t) 0) ∂(nLaw mN γ) := rfl

lemma costMFG_eq_VQ (M : Model T X Γ) (hM : M.Standing) (hA2 : M.A2) (u : Strat T X Γ → Strat T X Γ)
    (m : Meas X) (ρ : ProbabilityMeasure (Strat T X Γ × Flow T X)) :
    costMFG M m ρ u = VQ M u (Qcost M hM hA2 u) m ρ := rfl

/-- Along the subsequence, the player-1 functional converges to the mean field functional. -/
lemma tendsto_player_functional (M : Model T X Γ) (hM : M.Standing) (hA1a : M.A1a)
    (u : Strat T X Γ → Strat T X Γ) (G : GoodQ T X Γ) (m₀ : Meas X) (m0N : ℕ → Meas X)
    (γ : (N : ℕ) → ProbabilityMeasure (Fin N → Strat T X Γ)) (hA5 : Tendsto m0N atTop (𝓝 m₀))
    (ρ : ProbabilityMeasure (Strat T X Γ × Flow T X)) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hlim : Tendsto (rhoSeq M m0N γ ∘ φ) atTop (𝓝 ρ)) :
    Tendsto (fun k => ∫ ω, G.Q (fun t => nPath M 0 u ω t 0) (ω.2.1 0)
        (fun t => empOthers (nPath M 0 u ω t) 0)
          ∂(nLaw (prodInit (φ k + 2) (m0N (φ k + 2))) (γ (φ k + 2))))
      atTop (𝓝 (VQ M u G m₀ ρ)) := by
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hφ2 : Tendsto (fun k => φ k + 2) atTop atTop :=
    Filter.tendsto_atTop_mono (fun k => Nat.le_add_right (φ k) 2) hφt
  have hA := (claimA M hM hA1a u G m0N γ).comp hφt
  have hB := (claimB M hM hA1a u G m0N γ).comp hφt
  have hC := VQ_tendsto M hM hA1a u G (m := fun k => m0N (φ k + 2)) (hA5.comp hφ2)
    (ρs := fun k => rhoSeq M m0N γ (φ k)) hlim
  have := (hA.add hB).add hC
  simp only [zero_add] at this
  refine this.congr (fun k => ?_)
  simp only [Function.comp_apply]
  ring

theorem limit_points_optimal_OR (M : Model T X Γ) (hM : M.Standing) (hA1 : M.A1) (hA2 : M.A2)
    (m₀ : Meas X) (m0N : ℕ → Meas X) (γ : (N : ℕ) → ProbabilityMeasure (Fin N → Strat T X Γ))
    (ε : ℕ → ℝ) (hε : ∀ N, 0 ≤ ε N)
    (hA3 : ∀ N : ℕ, 2 ≤ N → IsSymmetric (γ N) ∧ IsEpsCE M (prodInit N (m0N N)) (γ N) (ε N))
    (hA4 : Tendsto ε atTop (𝓝 0))
    (hA5 : Tendsto m0N atTop (𝓝 m₀))
    (ρ : ProbabilityMeasure (Strat T X Γ × Flow T X))
    (hρ : ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (rhoSeq M m0N γ ∘ φ) atTop (𝓝 ρ)) :
    IsOptimal M m₀ ρ := by
  obtain ⟨φ, hφ, hlim⟩ := hρ
  intro u
  have hφ2 : Tendsto (fun k => φ k + 2) atTop atTop :=
    Filter.tendsto_atTop_mono (fun k => Nat.le_add_right (φ k) 2) hφ.tendsto_atTop
  have key : ∀ v : Strat T X Γ → Strat T X Γ, Tendsto (fun k =>
      costN M (prodInit (φ k + 2) (m0N (φ k + 2))) (γ (φ k + 2)) 0 v) atTop
      (𝓝 (costMFG M m₀ ρ v)) := by
    intro v
    rw [costMFG_eq_VQ M hM hA2 v]
    simp_rw [costN_eq_Qcost M hM hA2 v]
    exact tendsto_player_functional M hM hA1.1 v (Qcost M hM hA2 v) m₀ m0N γ hA5 ρ φ hφ hlim
  have hε' : Tendsto (fun k => ε (φ k + 2)) atTop (𝓝 0) := hA4.comp hφ2
  have hle : ∀ k, costN M (prodInit (φ k + 2) (m0N (φ k + 2))) (γ (φ k + 2)) 0 id ≤
      costN M (prodInit (φ k + 2) (m0N (φ k + 2))) (γ (φ k + 2)) 0 u + ε (φ k + 2) :=
    fun k => (hA3 (φ k + 2) (by omega)).2 0 u
  have := le_of_tendsto_of_tendsto (key id) ((key u).add hε') (Filter.Eventually.of_forall hle)
  simpa using this

end SecOpt

section SecCons
variable {T : ℕ} {X Γ : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    [TopologicalSpace X] [DiscreteTopology X]
    [MeasurableSpace X] [DiscreteMeasurableSpace X]
    [Fintype Γ] [Nonempty Γ] [MeasurableSpace Γ] [DiscreteMeasurableSpace Γ]
    [TopologicalSpace Γ] [DiscreteTopology Γ]

/-- The empirical measure of the others and of all players are `1/N`-close. -/
lemma distTV_empOthers_empAll {N : ℕ} [NeZero N] (hN : 2 ≤ N) (x : Fin N → X) :
    distTV (empOthers x 0) (empOn Finset.univ x) ≤ 1 / (N : ℝ) := by
  set S := Finset.univ.erase (0 : Fin N) with hS
  have hSc : S.card = N - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have hSne : S.Nonempty := by rw [← Finset.card_pos, hSc]; omega
  have hU : (Finset.univ : Finset (Fin N)).Nonempty := Finset.univ_nonempty_iff.mpr ⟨0⟩
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN1 : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  set c : X → ℝ := fun y => ∑ j ∈ S, (if x j = y then (1 : ℝ) else 0) with hc
  have hsplit : ∀ y, (∑ j, (if x j = y then (1 : ℝ) else 0)) = c y + (if x 0 = y then 1 else 0) := by
    intro y
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin N))]
    ring
  have hcsum : ∑ y, c y = (N : ℝ) - 1 := by
    simp only [hc]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hSc, hN1]
  have hc0 : ∀ y, 0 ≤ c y := fun y => Finset.sum_nonneg fun j _ => by split_ifs <;> norm_num
  have hi : ∀ y, |(empOthers x 0).1 y - (empOn Finset.univ x).1 y| ≤
      c y * (1 / ((N : ℝ) - 1) - 1 / N) + (if x 0 = y then 1 else 0) / N := by
    intro y
    simp only [empOthers]
    rw [empOn_apply' S hSne, empOn_apply' _ hU, hSc, hN1, Finset.card_univ, Fintype.card_fin, hsplit y]
    have hN0 : (0 : ℝ) < N - 1 := by linarith
    have hNp : (0 : ℝ) < N := by linarith
    have : 1 / ((N : ℝ) - 1) * c y - 1 / N * (c y + (if x 0 = y then 1 else 0)) =
        c y * (1 / ((N : ℝ) - 1) - 1 / N) - (if x 0 = y then 1 else 0) / N := by ring
    rw [this]
    refine (abs_sub _ _).trans ?_
    have h1 : 0 ≤ 1 / ((N : ℝ) - 1) - 1 / N := by
      rw [sub_nonneg]; exact one_div_le_one_div_of_le hN0 (by linarith)
    rw [abs_of_nonneg (mul_nonneg (hc0 y) h1), abs_of_nonneg (by split_ifs <;> positivity)]
  show (1 / 2 : ℝ) * ∑ y, |(empOthers x 0).1 y - (empOn Finset.univ x).1 y| ≤ 1 / N
  have hsum := Finset.sum_le_sum fun y (_ : y ∈ Finset.univ) => hi y
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hcsum, ← Finset.sum_div] at hsum
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true] at hsum
  have hN0 : (0 : ℝ) < N - 1 := by linarith
  have hNp : (0 : ℝ) < N := by linarith
  have h2 : ((N : ℝ) - 1) * (1 / ((N : ℝ) - 1) - 1 / N) + 1 / N = 2 / N := by
    field_simp; ring
  have h3 : (1 / 2 : ℝ) * (2 / N) = 1 / N := by field_simp
  rw [h2] at hsum
  calc (1 / 2 : ℝ) * ∑ y, |(empOthers x 0).1 y - (empOn Finset.univ x).1 y| ≤ 1 / 2 * (2 / N) := by
        gcongr
    _ = 1 / N := h3


/-- Exchangeability (Step Four, prelimit, with a bounded measurable test function of the flow of
empirical measures). -/
lemma exch_g (M : Model T X Γ) (hM : M.Standing) {N : ℕ} [NeZero N] (m : Meas X)
    (γ : ProbabilityMeasure (Fin N → Strat T X Γ)) (hγ : IsSymmetric γ) (t : Fin (T + 1)) (x : X)
    (g : Flow T X → ℝ) (hg : Measurable g) (C : ℝ) (hgC : ∀ μ, |g μ| ≤ C) :
    ∫ ω, g (fun s => empOn Finset.univ (nPath M 0 id ω s)) *
        (if nPath M 0 id ω t 0 = x then (1 : ℝ) else 0) ∂(nLaw (prodInit N m) γ) =
      ∫ ω, g (fun s => empOn Finset.univ (nPath M 0 id ω s)) *
        (empOn Finset.univ (nPath M 0 id ω t)).1 x ∂(nLaw (prodInit N m) γ) := by
  set P := nLaw (prodInit N m) γ with hP
  set μf : NOmega T N X Γ → Flow T X := fun ω s => empOn Finset.univ (nPath M 0 id ω s) with hμf
  have hpaths : Measurable (fun ω : NOmega T N X Γ => fun s => nPath M 0 id ω s) :=
    measurable_pi_lambda _ (fun s => measurable_nPath M hM 0 id s)
  have hμfm : Measurable μf :=
    (measurable_of_countable (fun p : Fin (T + 1) → Fin N → X => fun s => empOn Finset.univ (p s))).comp
      hpaths
  set F : Fin N → NOmega T N X Γ → ℝ := fun i ω =>
    g (μf ω) * (if nPath M 0 id ω t i = x then (1 : ℝ) else 0) with hF
  have hFm : ∀ i, Measurable (F i) := by
    intro i
    refine (hg.comp hμfm).mul ?_
    have : (fun ω : NOmega T N X Γ => if nPath M 0 id ω t i = x then (1 : ℝ) else 0) =
        (fun y : X => if y = x then (1 : ℝ) else 0) ∘ (fun ω => nPath M 0 id ω t i) := rfl
    rw [this]
    exact (measurable_of_countable _).comp ((measurable_pi_apply i).comp (measurable_nPath M hM 0 id t))
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hgC (μf (Classical.arbitrary _)))
  have hFi : ∀ i, Integrable (F i) P := fun i =>
    Integrable.of_bound (hFm i).aestronglyMeasurable C (ae_of_all _ fun ω => by
      simp only [hF, Real.norm_eq_abs, abs_mul]
      have h1 := hgC (μf ω)
      have h2 : |(if nPath M 0 id ω t i = x then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
      nlinarith [abs_nonneg (g (μf ω))])
  have hEq : ∀ i, ∫ ω, F i ω ∂P = ∫ ω, F 0 ω ∂P := by
    intro i
    have hmap : P.map (permΩ (Equiv.swap 0 i)) = P := nLaw_map_permΩ m γ hγ (Equiv.swap 0 i)
    conv_rhs => rw [← hmap]
    rw [integral_map (measurable_permΩ _).aemeasurable (hFm 0).aestronglyMeasurable]
    congr 1
    funext ω
    simp only [hF, hμf]
    rw [nPath_permΩ]
    have : ∀ s, empOn Finset.univ (nPath M 0 id (permΩ (Equiv.swap 0 i) ω) s) =
        empOn Finset.univ (nPath M 0 id ω s) := fun s => by
      rw [nPath_permΩ]; exact empOn_comp_equiv _ _ _ (by simp) _
    simp only [this, Function.comp_apply, Equiv.swap_apply_left]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hne : (Finset.univ : Finset (Fin N)).Nonempty := Finset.univ_nonempty_iff.mpr ⟨0⟩
  have hrhs : ∀ ω, g (μf ω) * (empOn Finset.univ (nPath M 0 id ω t)).1 x =
      (1 / (N : ℝ)) * ∑ i, F i ω := by
    intro ω
    rw [empOn_apply' _ hne, Finset.card_univ, Fintype.card_fin, Finset.mul_sum, Finset.mul_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hF]
    ring
  change ∫ ω, F 0 ω ∂P = ∫ ω, g (μf ω) * (empOn Finset.univ (nPath M 0 id ω t)).1 x ∂P
  rw [integral_congr_ae (ae_of_all _ hrhs), integral_const_mul,
    integral_finset_sum _ (fun i _ => hFi i)]
  simp_rw [hEq]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

end SecCons

section SecCons2
variable {T : ℕ} {X Γ : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    [TopologicalSpace X] [DiscreteTopology X]
    [MeasurableSpace X] [DiscreteMeasurableSpace X]
    [Fintype Γ] [Nonempty Γ] [MeasurableSpace Γ] [DiscreteMeasurableSpace Γ]
    [TopologicalSpace Γ] [DiscreteTopology Γ]

/-- The test functional `g(μ) 1_{X(t) = x}`. -/
noncomputable def Qg (g : BoundedContinuousFunction (Flow T X) ℝ) (t : Fin (T + 1)) (x : X) :
    GoodQ T X Γ where
  Q p _ μ := g μ * (if p t = x then 1 else 0)
  C := ‖g‖
  C_nonneg := norm_nonneg _
  bound p _ μ := by
    rw [abs_mul]
    have h1 : |g μ| ≤ ‖g‖ := by rw [← Real.norm_eq_abs]; exact g.norm_coe_le_norm μ
    have h2 : |(if p t = x then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
    nlinarith [abs_nonneg (g μ), norm_nonneg g]
  cont p _ := g.continuous.mul continuous_const

lemma continuous_coord (t : Fin (T + 1)) (x : X) :
    Continuous (fun μ : Flow T X => (μ t).1 x) :=
  (continuous_apply x).comp (continuous_subtype_val.comp (continuous_apply t))

lemma coord_mem (μ : Flow T X) (t : Fin (T + 1)) (x : X) : 0 ≤ (μ t).1 x ∧ (μ t).1 x ≤ 1 := by
  refine ⟨(μ t).2.1 x, ?_⟩
  have := Finset.single_le_sum (f := fun y => (μ t).1 y) (fun y _ => (μ t).2.1 y) (Finset.mem_univ x)
  rw [(μ t).2.2] at this
  exact this

/-- The key identity behind consistency, tested against bounded continuous functions of the flow. -/
lemma cons_key (M : Model T X Γ) (hM : M.Standing) (hA1a : M.A1a)
    (m₀ : Meas X) (m0N : ℕ → Meas X) (γ : (N : ℕ) → ProbabilityMeasure (Fin N → Strat T X Γ))
    (hsym : ∀ N : ℕ, 2 ≤ N → IsSymmetric (γ N))
    (hA5 : Tendsto m0N atTop (𝓝 m₀))
    (ρ : ProbabilityMeasure (Strat T X Γ × Flow T X)) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hlim : Tendsto (rhoSeq M m0N γ ∘ φ) atTop (𝓝 ρ))
    (g : BoundedContinuousFunction (Flow T X) ℝ) (t : Fin (T + 1)) (x : X) :
    VQ M id (Qg (Γ := Γ) g t x) m₀ ρ =
      ∫ q, g q.2 * (q.2 t).1 x ∂(ρ : Measure (Strat T X Γ × Flow T X)) := by
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hφ2 : Tendsto (fun k => φ k + 2) atTop atTop :=
    Filter.tendsto_atTop_mono (fun k => Nat.le_add_right (φ k) 2) hφt
  -- the player functional along the subsequence
  have h1 := tendsto_player_functional M hM hA1a id (Qg (Γ := Γ) g t x) m₀ m0N γ hA5 ρ φ hφ hlim
  -- the weak limit of `ρ^N`
  set G2 : Flow T X → ℝ := fun μ => g μ * (μ t).1 x with hG2
  have hG2c : Continuous G2 := g.continuous.mul (continuous_coord t x)
  have hG2b : ∀ μ, |G2 μ| ≤ ‖g‖ := by
    intro μ
    simp only [hG2, abs_mul]
    have h1 : |g μ| ≤ ‖g‖ := by rw [← Real.norm_eq_abs]; exact g.norm_coe_le_norm μ
    have h2 := coord_mem μ t x
    rw [abs_of_nonneg h2.1]
    nlinarith [abs_nonneg (g μ), norm_nonneg g]
  let G2b : BoundedContinuousFunction (Strat T X Γ × Flow T X) ℝ :=
    BoundedContinuousFunction.mkOfBound ⟨fun q => G2 q.2, hG2c.comp continuous_snd⟩ (2 * ‖g‖)
      (fun a b => by
        simp only [ContinuousMap.coe_mk, Real.dist_eq]
        have := abs_sub (G2 a.2) (G2 b.2); have := hG2b a.2; have := hG2b b.2
        linarith)
  have h2 := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim) G2b
  -- rewrite the approximating integrals on the `N`-player space
  have e2 : ∀ k, ∫ q, G2b q ∂((rhoSeq M m0N γ ∘ φ) k : Measure (Strat T X Γ × Flow T X)) =
      ∫ ω, G2 (fun s => empOthers (nPath M 0 id ω s) 0)
        ∂(nLaw (prodInit (φ k + 2) (m0N (φ k + 2))) (γ (φ k + 2))) := by
    intro k
    show ∫ q, G2b q ∂(rhoN M (prodInit (φ k + 2) (m0N (φ k + 2))) (γ (φ k + 2)) : Measure _) = _
    rw [rhoN_coe M hM, integral_map (measurable_rhoMap M hM).aemeasurable
      G2b.continuous.aestronglyMeasurable]
    rfl
  simp_rw [e2] at h2
  -- the difference of the two approximating sequences vanishes
  have h3 : Tendsto (fun k =>
      (∫ ω, (Qg (Γ := Γ) g t x).Q (fun s => nPath M 0 id ω s 0) (ω.2.1 0)
          (fun s => empOthers (nPath M 0 id ω s) 0)
          ∂(nLaw (prodInit (φ k + 2) (m0N (φ k + 2))) (γ (φ k + 2)))) -
        ∫ ω, G2 (fun s => empOthers (nPath M 0 id ω s) 0)
          ∂(nLaw (prodInit (φ k + 2) (m0N (φ k + 2))) (γ (φ k + 2)))) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨δ, hδ, hu⟩ := unif_family (fun b : Bool => if b then (g : Flow T X → ℝ) else G2)
      (fun b => by cases b <;> simp [hG2c, g.continuous]) (ε / 3) (by positivity)
    -- `N` large enough that the two flows are `δ`-close
    obtain ⟨K0, hK0⟩ : ∃ K0 : ℕ, ∀ k ≥ K0, 2 * ((T + 1 : ℕ) : ℝ) / ((φ k + 2 : ℕ) : ℝ) < δ := by
      have hlim0 : Tendsto (fun k => 2 * ((T + 1 : ℕ) : ℝ) / ((φ k + 2 : ℕ) : ℝ)) atTop (𝓝 0) := by
        have := (tendsto_natCast_atTop_atTop (R := ℝ)).comp hφ2
        have := this.const_div_atTop (2 * ((T + 1 : ℕ) : ℝ))
        simpa using this
      obtain ⟨K0, hK0⟩ := (Metric.tendsto_atTop.mp hlim0) δ hδ
      refine ⟨K0, fun k hk => ?_⟩
      have := hK0 k hk
      rw [Real.dist_eq, sub_zero] at this
      exact lt_of_abs_lt this
    refine ⟨K0, fun k hk => ?_⟩
    set N := φ k + 2 with hNdef
    have hN : 2 ≤ N := by omega
    set P := nLaw (prodInit N (m0N N)) (γ N) with hP
    rw [Real.dist_eq, sub_zero]
    set μ1 : NOmega T N X Γ → Flow T X := fun ω s => empOthers (nPath M 0 id ω s) 0 with hμ1
    set μa : NOmega T N X Γ → Flow T X := fun ω s => empOn Finset.univ (nPath M 0 id ω s) with hμa
    have hclose : ∀ ω, dist (μ1 ω) (μa ω) < δ := by
      intro ω
      refine lt_of_le_of_lt (dist_flow_le _ _) (lt_of_le_of_lt ?_ (hK0 k hk))
      have : ∀ s, distTV (μ1 ω s) (μa ω s) ≤ 1 / (N : ℝ) := fun s =>
        distTV_empOthers_empAll hN _
      calc 2 * ∑ s, distTV (μ1 ω s) (μa ω s) ≤ 2 * ∑ _s : Fin (T + 1), 1 / (N : ℝ) := by
            gcongr with s; exact this s
        _ = 2 * ((T + 1 : ℕ) : ℝ) / ((N : ℕ) : ℝ) := by
            simp [Finset.sum_const, Finset.card_univ]; ring
    have hpaths : Measurable (fun ω : NOmega T N X Γ => fun s => nPath M 0 id ω s) :=
      measurable_pi_lambda _ (fun s => measurable_nPath M hM 0 id s)
    have hμ1m : Measurable μ1 :=
      (measurable_of_countable (fun p : Fin (T + 1) → Fin N → X => fun s => empOthers (p s) 0)).comp hpaths
    have hμam : Measurable μa :=
      (measurable_of_countable (fun p : Fin (T + 1) → Fin N → X => fun s => empOn Finset.univ (p s))).comp
        hpaths
    set ind : NOmega T N X Γ → ℝ := fun ω => if nPath M 0 id ω t 0 = x then (1 : ℝ) else 0 with hind
    have hindm : Measurable ind := by
      have : ind = (fun y : X => if y = x then (1 : ℝ) else 0) ∘ (fun ω => nPath M 0 id ω t 0) := rfl
      rw [this]
      exact (measurable_of_countable _).comp ((measurable_pi_apply 0).comp (measurable_nPath M hM 0 id t))
    have hind01 : ∀ ω, 0 ≤ ind ω ∧ ind ω ≤ 1 := fun ω => by simp only [hind]; split_ifs <;> norm_num
    have hgb : ∀ μ, |g μ| ≤ ‖g‖ := fun μ => by rw [← Real.norm_eq_abs]; exact g.norm_coe_le_norm μ
    have bnd : ∀ (f : NOmega T N X Γ → ℝ), Measurable f → (∀ ω, |f ω| ≤ ‖g‖) → Integrable f P :=
      fun f hf hb => Integrable.of_bound hf.aestronglyMeasurable ‖g‖ (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs]; exact hb ω)
    have iA : Integrable (fun ω => g (μ1 ω) * ind ω) P :=
      bnd _ ((g.continuous.measurable.comp hμ1m).mul hindm) fun ω => by
        rw [abs_mul, abs_of_nonneg (hind01 ω).1]; nlinarith [hgb (μ1 ω), hind01 ω, abs_nonneg (g (μ1 ω))]
    have iA' : Integrable (fun ω => g (μa ω) * ind ω) P :=
      bnd _ ((g.continuous.measurable.comp hμam).mul hindm) fun ω => by
        rw [abs_mul, abs_of_nonneg (hind01 ω).1]; nlinarith [hgb (μa ω), hind01 ω, abs_nonneg (g (μa ω))]
    have iB : Integrable (fun ω => G2 (μ1 ω)) P := bnd _ (hG2c.measurable.comp hμ1m) fun ω => hG2b _
    have iB' : Integrable (fun ω => g (μa ω) * (μa ω t).1 x) P :=
      bnd _ (hG2c.measurable.comp hμam) fun ω => hG2b _
    -- exchangeability
    have hex := exch_g M hM (m0N N) (γ N) (hsym N hN) t x g g.continuous.measurable ‖g‖ hgb
    -- the two closeness estimates
    have hA : |∫ ω, g (μ1 ω) * ind ω ∂P - ∫ ω, g (μa ω) * ind ω ∂P| ≤ ε / 3 := by
      rw [← integral_sub iA iA']
      refine (abs_integral_le_integral_abs).trans ?_
      have : ∫ ω, |g (μ1 ω) * ind ω - g (μa ω) * ind ω| ∂P ≤ ∫ _ω, ε / 3 ∂P :=
        integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) (integrable_const _)
          (ae_of_all _ fun ω => by
            show |g (μ1 ω) * ind ω - g (μa ω) * ind ω| ≤ ε / 3
            rw [← sub_mul, abs_mul, abs_of_nonneg (hind01 ω).1]
            have := (hu true (μ1 ω) (μa ω) (hclose ω)).le
            simp only [if_true] at this
            nlinarith [hind01 ω, abs_nonneg (g (μ1 ω) - g (μa ω))])
      simpa using this
    have hB : |∫ ω, g (μa ω) * (μa ω t).1 x ∂P - ∫ ω, G2 (μ1 ω) ∂P| ≤ ε / 3 := by
      rw [← integral_sub iB' iB]
      refine (abs_integral_le_integral_abs).trans ?_
      have : ∫ ω, |g (μa ω) * (μa ω t).1 x - G2 (μ1 ω)| ∂P ≤ ∫ _ω, ε / 3 ∂P :=
        integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) (integrable_const _)
          (ae_of_all _ fun ω => by
            have := (hu false (μa ω) (μ1 ω) (by rw [dist_comm]; exact hclose ω)).le
            simp only [Bool.false_eq_true, if_false, hG2] at this
            exact this)
      simpa using this
    have hQ : ∫ ω, (Qg (Γ := Γ) g t x).Q (fun s => nPath M 0 id ω s 0) (ω.2.1 0)
        (fun s => empOthers (nPath M 0 id ω s) 0) ∂P = ∫ ω, g (μ1 ω) * ind ω ∂P := rfl
    have hex' : ∫ ω, g (μa ω) * ind ω ∂P = ∫ ω, g (μa ω) * (μa ω t).1 x ∂P := hex
    rw [hQ]
    calc |∫ ω, g (μ1 ω) * ind ω ∂P - ∫ ω, G2 (μ1 ω) ∂P|
        ≤ |∫ ω, g (μ1 ω) * ind ω ∂P - ∫ ω, g (μa ω) * ind ω ∂P| +
          |∫ ω, g (μa ω) * ind ω ∂P - ∫ ω, G2 (μ1 ω) ∂P| := abs_sub_le _ _ _
      _ = |∫ ω, g (μ1 ω) * ind ω ∂P - ∫ ω, g (μa ω) * ind ω ∂P| +
          |∫ ω, g (μa ω) * (μa ω t).1 x ∂P - ∫ ω, G2 (μ1 ω) ∂P| := by rw [hex']
      _ ≤ ε / 3 + ε / 3 := add_le_add hA hB
      _ < ε := by linarith
  -- conclude by uniqueness of limits
  have h4 := h1.sub h3
  simp only [sub_sub_cancel, sub_zero] at h4
  exact tendsto_nhds_unique h4 h2

end SecCons2

section SecCons3
variable {T : ℕ} {X Γ : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    [TopologicalSpace X] [DiscreteTopology X]
    [MeasurableSpace X] [DiscreteMeasurableSpace X]
    [Fintype Γ] [Nonempty Γ] [MeasurableSpace Γ] [DiscreteMeasurableSpace Γ]
    [TopologicalSpace Γ] [DiscreteTopology Γ]

theorem limit_points_consistent_OR (M : Model T X Γ) (hM : M.Standing) (hA1 : M.A1) (hA2 : M.A2)
    (m₀ : Meas X) (m0N : ℕ → Meas X) (γ : (N : ℕ) → ProbabilityMeasure (Fin N → Strat T X Γ))
    (ε : ℕ → ℝ) (hε : ∀ N, 0 ≤ ε N)
    (hA3 : ∀ N : ℕ, 2 ≤ N → IsSymmetric (γ N) ∧ IsEpsCE M (prodInit N (m0N N)) (γ N) (ε N))
    (hA4 : Tendsto ε atTop (𝓝 0))
    (hA5 : Tendsto m0N atTop (𝓝 m₀))
    (ρ : ProbabilityMeasure (Strat T X Γ × Flow T X))
    (hρ : ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (rhoSeq M m0N γ ∘ φ) atTop (𝓝 ρ)) :
    IsConsistent M m₀ ρ := by
  obtain ⟨φ, hφ, hlim⟩ := hρ
  intro t x B hB
  set L := mfgLaw m₀ ρ with hL
  set E : Set (MOmega T X Γ) := {ω | mfgPath M id ω t = x} with hE
  have hEm : MeasurableSet E := (measurable_mfgPath M hM id t) (measurableSet_singleton x)
  have hproj : Measurable (fun ω : MOmega T X Γ => ω.2.1.2) :=
    measurable_snd.comp (measurable_fst.comp measurable_snd)
  set dens : Flow T X → NNReal := fun μ => ⟨(μ t).1 x, (coord_mem μ t x).1⟩ with hdens
  have hdensm : Measurable dens :=
    ((continuous_coord t x).measurable).subtype_mk
  set ρ2 : Measure (Flow T X) := (ρ : Measure (Strat T X Γ × Flow T X)).map Prod.snd with hρ2
  set lam1 : Measure (Flow T X) := (L.restrict E).map (fun ω => ω.2.1.2) with hlam1
  set lam2 : Measure (Flow T X) := ρ2.withDensity (fun μ => (dens μ : ENNReal)) with hlam2
  haveI : IsProbabilityMeasure ρ2 := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  haveI : IsFiniteMeasure lam1 := by rw [hlam1]; infer_instance
  haveI : IsFiniteMeasure lam2 := by
    refine isFiniteMeasure_withDensity ?_
    refine ne_top_of_le_ne_top (b := ∫⁻ _μ, (1 : ENNReal) ∂ρ2) (by simp) (lintegral_mono fun μ => ?_)
    have : dens μ ≤ 1 := by rw [← NNReal.coe_le_coe]; exact (coord_mem μ t x).2
    exact ENNReal.coe_le_one_iff.mpr this
  have heq : lam1 = lam2 := by
    refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun g => ?_
    rw [hlam1, hlam2, integral_map hproj.aemeasurable g.continuous.aestronglyMeasurable,
      integral_withDensity_eq_integral_smul hdensm]
    have hfun : (fun q : Flow T X => dens q • g q) = fun q => (q t).1 x * g q :=
      funext fun q => by rw [NNReal.smul_def, smul_eq_mul]; rfl
    have hm2 : AEStronglyMeasurable (fun q : Flow T X => (q t).1 x * g q)
        ((ρ : Measure (Strat T X Γ × Flow T X)).map Prod.snd) :=
      ((continuous_coord t x).mul g.continuous).aestronglyMeasurable
    rw [hfun, hρ2, integral_map measurable_snd.aemeasurable hm2]
    have hk := cons_key M hM hA1.1 m₀ m0N γ (fun N hN => (hA3 N hN).1) hA5 ρ φ hφ hlim g t x
    have lhs : ∫ ω in E, g ω.2.1.2 ∂L = VQ M id (Qg (Γ := Γ) g t x) m₀ ρ := by
      rw [← integral_indicator hEm]
      unfold VQ
      congr 1
      funext ω
      simp only [Qg, hE, Set.indicator_apply, Set.mem_setOf_eq]
      split_ifs <;> simp
    rw [lhs, hk]
    congr 1
    funext q
    ring
  -- evaluate at `B`
  have h1 : lam1 B = L {ω | mfgPath M id ω t = x ∧ ω.2.1.2 ∈ B} := by
    rw [hlam1, Measure.map_apply hproj hB, Measure.restrict_apply (hproj hB)]
    congr 1
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, hE, Set.mem_setOf_eq]
    exact and_comm
  have h2 : lam2 B = ∫⁻ μ in B, (dens μ : ENNReal) ∂ρ2 := by
    rw [hlam2, withDensity_apply _ hB]
  have hind : Measurable (B.indicator (fun m : Flow T X => (m t).1 x)) :=
    (continuous_coord t x).measurable.indicator hB
  show L.real {ω | mfgPath M id ω t = x ∧ ω.2.1.2 ∈ B} =
    ∫ p, B.indicator (fun m : Flow T X => (m t).1 x) p.2 ∂(ρ : Measure (Strat T X Γ × Flow T X))
  rw [measureReal_def, ← h1, heq, h2]
  rw [show (∫ p, B.indicator (fun m : Flow T X => (m t).1 x) p.2 ∂(ρ : Measure (Strat T X Γ × Flow T X)))
      = ∫ μ, B.indicator (fun m : Flow T X => (m t).1 x) μ ∂ρ2 by
    rw [hρ2, integral_map measurable_snd.aemeasurable hind.aestronglyMeasurable]]
  rw [integral_indicator hB, integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ fun μ => (coord_mem μ t x).1)
    (continuous_coord t x).measurable.aestronglyMeasurable]
  congr 1
  refine lintegral_congr fun μ => ?_
  simp only [hdens]
  rw [ENNReal.ofReal_eq_coe_nnreal (coord_mem μ t x).1]
  rfl

end SecCons3


theorem solution {T : ℕ} {X Γ : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    [TopologicalSpace X] [DiscreteTopology X] [MeasurableSpace X] [DiscreteMeasurableSpace X]
    [Fintype Γ] [Nonempty Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] [MeasurableSpace Γ]
    [DiscreteMeasurableSpace Γ]
    (M : Model T X Γ) (hM : M.Standing) (hA1 : M.A1) (hA2 : M.A2)
    (m₀ : Meas X) (m0N : ℕ → Meas X) (γ : (N : ℕ) → ProbabilityMeasure (Fin N → Strat T X Γ))
    (ε : ℕ → ℝ) (hε : ∀ N, 0 ≤ ε N)
    (hA3 : ∀ N : ℕ, 2 ≤ N → IsSymmetric (γ N) ∧ IsEpsCE M (prodInit N (m0N N)) (γ N) (ε N))
    (hA4 : Tendsto ε atTop (𝓝 0))
    (hA5 : Tendsto m0N atTop (𝓝 m₀))
    (ρ : ProbabilityMeasure (Strat T X Γ × Flow T X))
    (hρ : ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (rhoSeq M m0N γ ∘ φ) atTop (𝓝 ρ)) :
    IsConsistent M m₀ ρ :=
  limit_points_consistent_OR M hM hA1 hA2 m₀ m0N γ ε hε hA3 hA4 hA5 ρ hρ
