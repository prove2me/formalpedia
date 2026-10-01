-- Prove2me | solution 1 for RobustMDP.Stationarity.nominal_stationarity
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T12:13:02.768594+00:00
-- url     : https://prove2.me/submissions/5534550e-43ae-4d24-a2cc-5513e0da8da0

import Theorems.Thm_RobustMDP_Stationarity_stationary_policies_suffice
import Definitions.Def_RobustMDP_Stationarity_gameValues
import Mathlib.Order.ConditionallyCompleteLattice.Group
import Mathlib.Tactic
open RobustMDP.Stationarity Filter Topology
namespace CStationary

theorem state_simplex {n : ℕ} {A : Type} (M : Model n A) (i₀ : Fin n)
    (π : Policy n A) (τ : M.NaturePolicy) : ∀ t, M.stateDist i₀ π τ t∈stdSimplex ℝ (Fin n) := by
  intro t
  induction t with
  | zero => simpa [Model.stateDist,eq_comm] using ite_eq_mem_stdSimplex ℝ i₀
  | succ t ih =>
    have hp : ∀ i, (τ t).1 (π t i) i∈stdSimplex ℝ (Fin n) :=
      fun i => M.rows_subset_simplex _ _ ((τ t).2 _ _)
    constructor
    · intro j
      exact Finset.sum_nonneg (fun i _ => mul_nonneg (ih.1 i) ((hp i).1 j))
    · simp only [Model.stateDist]
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum,(hp _).2,mul_one]
      exact ih.2

theorem cost_le_cmax {n : ℕ} {A : Type} [Fintype A] (M : Model n A) (i : Fin n) (a : A) :
    M.cost i a ≤ M.cmax :=
  (le_ciSup (Set.finite_range (M.cost i)).bddAbove a).trans
    (le_ciSup (Set.finite_range (fun i => ⨆ a, M.cost i a)).bddAbove i)

theorem stage_bounds {n : ℕ} {A : Type} [Fintype A] (M : Model n A) (ν : ℝ)
    (hν : 0 ≤ ν) (i₀ : Fin n) (π : Policy n A) (τ : M.NaturePolicy) (t : ℕ) :
    0 ≤ M.stageCost ν i₀ π τ t ∧ M.stageCost ν i₀ π τ t ≤ ν^t*M.cmax := by
  have hp := state_simplex M i₀ π τ t
  constructor
  · exact mul_nonneg (pow_nonneg hν _) (Finset.sum_nonneg (fun i _ => mul_nonneg (hp.1 i) (M.cost_nonneg _ _)))
  · apply mul_le_mul_of_nonneg_left _ (pow_nonneg hν _)
    calc
      _ ≤ ∑ i, M.stateDist i₀ π τ t i*M.cmax := Finset.sum_le_sum (fun i _ =>
        mul_le_mul_of_nonneg_left (cost_le_cmax M i (π t i)) (hp.1 i))
      _ = _ := by rw [← Finset.sum_mul,hp.2,one_mul]

theorem series_tail (f : ℕ → ℝ) (ν C : ℝ) (hν0 : 0 ≤ ν) (hν1 : ν < 1)
    (hf0 : ∀ t, 0 ≤ f t) (hbound : ∀ t, f t ≤ ν^t*C) (N : ℕ) :
    (∑ t∈Finset.range N, f t) ≤ ∑' t, f t ∧
      (∑' t, f t) ≤ (∑ t∈Finset.range N, f t)+ν^N*C/(1-ν) := by
  have hg := (hasSum_geometric_of_lt_one hν0 hν1).mul_right C
  have hf : Summable f := Summable.of_nonneg_of_le hf0 hbound hg.summable
  refine ⟨hf.sum_le_tsum _ (fun t _ => hf0 t),?_⟩
  have htail := Summable.tsum_le_tsum (fun t => hbound (t+N))
    ((summable_nat_add_iff N).mpr hf) ((summable_nat_add_iff N).mpr hg.summable)
  have hts : (∑' t : ℕ, ν^(t+N)*C)=ν^N*C/(1-ν) := by
    have hh := (hasSum_geometric_of_lt_one hν0 hν1).mul_right (ν^N*C)
    convert! hh.tsum_eq using 1
    · congr 1
      ext t
      rw [pow_add]
      ring
    · ring
  rw [hts] at htail
  have hdecomp := hf.sum_add_tsum_nat_add N
  linarith

theorem truncation {n : ℕ} {A : Type} [Fintype A] (M : Model n A) (ν : ℝ)
    (hν0 : 0 ≤ ν) (hν1 : ν < 1) (i₀ : Fin n) (π : Policy n A) (τ : M.NaturePolicy) (N : ℕ) :
    M.finiteCost ν i₀ N π τ ≤ M.infCost ν i₀ π τ ∧
      M.infCost ν i₀ π τ ≤ M.finiteCost ν i₀ N π τ+M.epsN ν N :=
  series_tail (M.stageCost ν i₀ π τ) ν M.cmax hν0 hν1
    (fun t => (stage_bounds M ν hν0 i₀ π τ t).1) (fun t => (stage_bounds M ν hν0 i₀ π τ t).2) N
end CStationary

namespace CStationary

theorem minmax_bounds {I J : Type*} [Nonempty I] [Nonempty J] (F G : I → J → ℝ)
    (U eps : ℝ) (hF : ∀ i j, 0 ≤ F i j) (hFG : ∀ i j, F i j ≤ G i j)
    (hG : ∀ i j, G i j ≤ U) (hclose : ∀ i j, G i j ≤ F i j+eps) :
    (⨅ i, ⨆ j, F i j) ≤ (⨅ i, ⨆ j, G i j) ∧
      (⨅ i, ⨆ j, G i j) ≤ (⨅ i, ⨆ j, F i j)+eps := by
  classical
  have hBF : ∀ i, BddAbove (Set.range (F i)) := fun i => ⟨U,by rintro x ⟨j,rfl⟩; exact (hFG i j).trans (hG i j)⟩
  have hBG : ∀ i, BddAbove (Set.range (G i)) := fun i => ⟨U,by rintro x ⟨j,rfl⟩; exact hG i j⟩
  have hNF : ∀ i, 0 ≤ ⨆ j, F i j := by
    intro i
    exact (hF i (Classical.choice (inferInstance : Nonempty J))).trans (le_ciSup (hBF i) _)
  have hNG : ∀ i, 0 ≤ ⨆ j, G i j := by
    intro i
    exact ((hF i (Classical.choice (inferInstance : Nonempty J))).trans (hFG i _)).trans (le_ciSup (hBG i) _)
  have hLF : BddBelow (Set.range (fun i => ⨆ j, F i j)) := ⟨0,by rintro x ⟨i,rfl⟩; exact hNF i⟩
  have hLG : BddBelow (Set.range (fun i => ⨆ j, G i j)) := ⟨0,by rintro x ⟨i,rfl⟩; exact hNG i⟩
  constructor
  · exact ciInf_mono hLF (fun i => ciSup_mono (hBG i) (hFG i))
  · apply le_ciInf_add
    intro i
    apply (ciInf_le hLG i).trans
    apply ciSup_le
    intro j
    exact (hclose i j).trans (add_le_add_left (le_ciSup (hBF i) j) eps)

theorem choice_nonempty {n : ℕ} {A : Type} (M : Model n A) : Nonempty M.Choice := by
  classical
  exact ⟨⟨fun a i => (M.rows_nonempty a i).choose,fun a i => (M.rows_nonempty a i).choose_spec⟩⟩

theorem inf_upper {n : ℕ} {A : Type} [Fintype A] (M : Model n A) (ν : ℝ)
    (hν0 : 0 ≤ ν) (hν1 : ν < 1) (i₀ : Fin n) (π : Policy n A) (τ : M.NaturePolicy) :
    M.infCost ν i₀ π τ ≤ M.cmax/(1-ν) := by
  have h := (truncation M ν hν0 hν1 i₀ π τ 0).2
  simpa [Model.finiteCost,Model.epsN] using h
end CStationary

namespace CStationary


theorem inf_congr {n : ℕ} {A B : Type} (M : Model n A) (M' : Model n B) (ν : ℝ) (i₀ : Fin n)
    (π : Policy n A) (π' : Policy n B) (τ : M.NaturePolicy) (τ' : M'.NaturePolicy)
    (hc : ∀ t i, M.cost i (π t i)=M'.cost i (π' t i))
    (hp : ∀ t i, (τ t).1 (π t i) i=(τ' t).1 (π' t i) i) :
    M.infCost ν i₀ π τ=M'.infCost ν i₀ π' τ' := by
  have hstate : ∀ t, M.stateDist i₀ π τ t=M'.stateDist i₀ π' τ' t := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      funext j
      simp only [Model.stateDist,ih]
      exact Finset.sum_congr rfl (fun i _ => by rw [hp])
  simp only [Model.infCost,Model.stageCost,hstate,hc]

theorem sup_eq_of_maps {I J : Type*} (f : I → ℝ) (g : J → ℝ)
    (r : I → J) (e : J → I) (hr : ∀ i, f i=g (r i)) (he : ∀ j, f (e j)=g j) :
    (⨆ i, f i)=⨆ j, g j := by
  have hh : Set.range f=Set.range g := by
    ext x
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨r i,(hr i).symm⟩
    · rintro ⟨j,rfl⟩
      exact ⟨e j,he j⟩
  exact congrArg sSup hh

end CStationary

theorem solution {n : ℕ} {A : Type} [Fintype A] [Nonempty A]
    (M : Model n A) (ν : ℝ) (hν₀ : 0 < ν) (hν₁ : ν < 1) (i₀ : Fin n) (P : M.Choice) :
    Filter.Tendsto (fun N : ℕ => ⨅ π : Policy n A, M.finiteCost ν i₀ N π (fun _ => P))
      Filter.atTop
      (nhds (⨅ π : Fin n → A, M.infCost ν i₀ (fun _ => π) (fun _ => P))) := by
  classical
  let M' : Model n A := {
    cost := M.cost
    rows := fun a i => {P.1 a i}
    cost_nonneg := M.cost_nonneg
    rows_subset_simplex := fun a i => by
      intro x hx
      obtain rfl := Set.mem_singleton_iff.mp hx
      exact M.rows_subset_simplex a i (P.2 a i)
    rows_nonempty := fun a i => Set.singleton_nonempty _ }
  let P' : M'.Choice := ⟨P.1,fun _ _ => rfl⟩
  have hu : ∀ Q : M'.Choice, Q=P' := by
    intro Q
    apply Subtype.ext
    funext a i
    exact Q.2 a i
  letI : Nonempty M'.Choice := ⟨P'⟩
  have hτ : ∀ τ : M'.NaturePolicy, τ=fun _ => P' := by
    intro τ
    funext t
    exact hu (τ t)
  have hcost : ∀ π : Policy n A, M'.infCost ν i₀ π (fun _ => P')=M.infCost ν i₀ π (fun _ => P) := by
    intro π
    exact CStationary.inf_congr M' M ν i₀ _ _ _ _ (fun _ _ => rfl) (fun _ _ => rfl)
  have hstat : (⨅ π : Policy n A, M.infCost ν i₀ π (fun _ => P))=
      ⨅ π : Fin n → A, M.infCost ν i₀ (fun _ => π) (fun _ => P) := by
    have h := (stationary_policies_suffice M' ν hν₀ hν₁ i₀).1.1
    simpa only [Model.phiInf_PT,Model.phiInf_PsTs,hτ,hu,ciSup_const,hcost] using h
  let v : ℝ := ⨅ π : Policy n A, M.infCost ν i₀ π (fun _ => P)
  have hb : ∀ N : ℕ,
      (⨅ π : Policy n A, M.finiteCost ν i₀ N π (fun _ => P)) ≤ v ∧
      v ≤ (⨅ π : Policy n A, M.finiteCost ν i₀ N π (fun _ => P))+M.epsN ν N := by
    intro N
    have h := CStationary.minmax_bounds
      (fun (π : Policy n A) (_ : Unit) => M.finiteCost ν i₀ N π (fun _ => P))
      (fun (π : Policy n A) (_ : Unit) => M.infCost ν i₀ π (fun _ => P))
      (M.cmax/(1-ν)) (M.epsN ν N)
      (fun π _ => Finset.sum_nonneg (fun t _ => (CStationary.stage_bounds M ν hν₀.le i₀ π (fun _ => P) t).1))
      (fun π _ => (CStationary.truncation M ν hν₀.le hν₁ i₀ π (fun _ => P) N).1)
      (fun π _ => CStationary.inf_upper M ν hν₀.le hν₁ i₀ π (fun _ => P))
      (fun π _ => (CStationary.truncation M ν hν₀.le hν₁ i₀ π (fun _ => P) N).2)
    simpa only [ciSup_const] using h
  have ht : Tendsto (M.epsN ν) atTop (𝓝 0) := by
    change Tendsto (fun N : ℕ => ν^N*M.cmax/(1-ν)) atTop (𝓝 0)
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hν₀.le hν₁).mul_const M.cmax).div_const (1-ν)
  rw [← hstat]
  have hv : Tendsto (fun N => v-M.epsN ν N) atTop (𝓝 v) := by
    simpa using tendsto_const_nhds.sub ht
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hv tendsto_const_nhds
    (fun N => by have h := (hb N).2; linarith) (fun N => (hb N).1)
