-- Prove2me | solution 2 for OnDemandDelivery.RouteElim.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T14:54:45.770073+00:00
-- url     : https://prove2.me/submissions/fca04d2f-aa4c-4622-aaf5-b211e263b899

import Mathlib
import Definitions.Def_OnDemandDelivery_RouteElim_Setting
import Theorems.Thm_LinearOptimization_farkas_inequality_form_fintype
import Theorems.Thm_OnDemandDelivery_RouteElim_rf1r_dual_bound
import Theorems.Thm_OnDemandDelivery_RouteElim_eq74

-- carved verbatim out of submission bc801293-ec4d-46a4-9496-25af5f48662e, lines 355-363

section
open Finset OnDemandDelivery.RouteElim
set_option maxHeartbeats 1000000

lemma route_sum_identity {R I P : Type} [Fintype R] [Fintype I] [Fintype P]
    (D : Data R I P) (S : Finset I) (μ : P → ℝ) (μn : ℝ) (ν : I → ℝ) (θ : R → ℝ) :
    (∑ s, θ s * ((∑ i ∈ S, D.α i s * ν i) + (∑ p, D.β p s * μ p) + μn)) =
      (∑ i ∈ S, ν i * (∑ s, D.α i s * θ s)) +
      (∑ p, μ p * (∑ s, D.β p s * θ s)) + μn * ∑ s, θ s := by
  simp_rw [mul_add, sum_add_distrib]
  congr 1
  · congr 1
    · simp_rw [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro s _
      ring
    · simp_rw [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro p _
      apply sum_congr rfl
      intro s _
      ring
  · rw [mul_sum]
    apply sum_congr rfl
    intro s _
    ring

lemma route_bound_identity {R I P : Type} [Fintype R] [Fintype I] [Fintype P]
    (D : Data R I P) (hD : D.Standing) (r : R) (μ : P → ℝ) (μn : ℝ) (ν : I → ℝ) :
    D.c r + D.rf1rBound r μ μn ν = D.dualObjective μ μn ν + D.reducedCost μ μn ν r := by
  classical
  have hsum : (∑ i ∈ univ.filter (fun i => D.α i r = 0), ν i) = (∑ i, ν i) - ∑ i, D.α i r * ν i := by
    rw [← sum_sub_distrib, sum_filter]
    apply sum_congr rfl
    intro i _
    rcases hD.1 i r with h | h <;> simp [h]
  dsimp [Data.rf1rBound, Data.dualObjective, Data.reducedCost]
  rw [hsum]
  ring

lemma route_weak {R I P : Type} [Fintype R] [Fintype I] [Fintype P]
    (D : Data R I P) (θ : R → ℝ) (hθ : D.RF1Feasible θ)
    (μ : P → ℝ) (μn : ℝ) (ν : I → ℝ) (hd : D.DualFeasible μ μn ν) :
    D.dualObjective μ μn ν ≤ D.cost θ := by
  classical
  have hcost : (∑ s, θ s * ((∑ i ∈ (univ : Finset I), D.α i s * ν i) + (∑ p, D.β p s * μ p) + μn)) ≤ D.cost θ := by
    apply sum_le_sum
    intro s _
    exact mul_le_mul_of_nonneg_left (hd.2.2.2 s) (hθ.2.2.2 s)
  rw [route_sum_identity] at hcost
  have hc : (∑ i, ν i) ≤ ∑ i, ν i * (∑ s, D.α i s * θ s) := by
    apply sum_le_sum
    intro i _
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hθ.2.2.1 i) (hd.2.2.1 i)
  have hp : (∑ p, μ p * D.b p) ≤ ∑ p, μ p * (∑ s, D.β p s * θ s) := by
    apply sum_le_sum
    intro p _
    exact mul_le_mul_of_nonpos_left (hθ.1 p) (hd.1 p)
  have hn := mul_le_mul_of_nonpos_left hθ.2.1 hd.2.1
  dsimp [Data.dualObjective]
  linarith

lemma route_equivalence_using_value {R I P : Type} [Fintype R] [Fintype I] [Fintype P]
    (D : Data R I P) (hD : D.Standing) (φ : ℝ)
    (μ : P → ℝ) (μn : ℝ) (ν : I → ℝ) (hvalue : D.dualObjective μ μn ν = φ)
    (ub : ℝ) (r : R) :
    ub < D.c r + D.rf1rBound r μ μn ν ↔ ub - φ < D.reducedCost μ μn ν r := by
  have hid := route_bound_identity D hD r μ μn ν
  rw [hvalue] at hid
  constructor <;> intro h <;> linarith

lemma route_root_using_value {R I P : Type} [Fintype R] [Fintype I] [Fintype P]
    (D : Data R I P) (hD : D.Standing)
    (ub : ℝ) (hub : ∀ θ, D.SF1Optimal θ → D.cost θ ≤ ub) (φ : ℝ)
    (μ : P → ℝ) (μn : ℝ) (ν : I → ℝ) (hdual : D.DualOptimal μ μn ν)
    (hvalue : D.dualObjective μ μn ν = φ)
    (r : R) (h33 : ub - φ < D.reducedCost μ μn ν r) :
    ∀ θ, D.SF1Optimal θ → θ r = 0 := by
  have hreal := (route_equivalence_using_value D hD φ μ μn ν hvalue ub r).mpr h33
  have hbound := (OnDemandDelivery.RouteElim.rf1r_dual_bound D hD μ μn ν hdual.1 r).2.2
  apply OnDemandDelivery.RouteElim.eq74 D hD ub hub r
  have he : (ub : EReal) < ((D.c r + D.rf1rBound r μ μn ν : ℝ) : EReal) := by exact_mod_cast hreal
  rw [EReal.coe_add] at he
  exact he.trans_le (add_le_add le_rfl hbound)

end

section
open Finset OnDemandDelivery.RouteElim
set_option maxHeartbeats 1000000
open Matrix Finset

lemma route_farkas {ι κ : Type} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℝ) (b : ι → ℝ) (c : κ → ℝ) (d : ℝ)
    (hfeas : ∃ x : κ → ℝ, A.mulVec x ≤ b)
    (hvalid : ∀ x : κ → ℝ, A.mulVec x ≤ b → c ⬝ᵥ x ≤ d) :
    ∃ p : ι → ℝ, 0 ≤ p ∧ Aᵀ.mulVec p = c ∧ p ⬝ᵥ b ≤ d := by
  classical
  let e : κ ≃ Fin (Fintype.card κ) := Fintype.equivFin κ
  let A' : Matrix ι (Fin (Fintype.card κ)) ℝ := fun i j => A i (e.symm j)
  let c' : Fin (Fintype.card κ) → ℝ := fun j => c (e.symm j)
  have hrow (x : Fin (Fintype.card κ) → ℝ) :
      A'.mulVec x = A.mulVec (fun r => x (e r)) := by
    funext i
    change (∑ j, A i (e.symm j) * x j) = ∑ r, A i r * x (e r)
    simpa using (e.sum_comp (fun j => A i (e.symm j) * x j)).symm
  have hdot (x : Fin (Fintype.card κ) → ℝ) :
      c' ⬝ᵥ x = c ⬝ᵥ (fun r => x (e r)) := by
    change (∑ j, c (e.symm j) * x j) = ∑ r, c r * x (e r)
    simpa using (e.sum_comp (fun j => c (e.symm j) * x j)).symm
  have hf : ∃ x : Fin (Fintype.card κ) → ℝ, A'.mulVec x ≤ b := by
    obtain ⟨x, hx⟩ := hfeas
    refine ⟨fun j => x (e.symm j), ?_⟩
    rw [hrow]
    simpa using hx
  have hv : ∀ x, A'.mulVec x ≤ b → c' ⬝ᵥ x ≤ d := by
    intro x hx
    rw [hdot]
    exact hvalid _ (by simpa only [hrow] using hx)
  obtain ⟨p, hp, hstat, hobj⟩ :=
    (LinearOptimization.farkas_inequality_form_fintype A' b c' d hf).mp hv
  refine ⟨p, hp, ?_, hobj⟩
  funext r
  have hr := congrFun hstat (e r)
  change (∑ i, A i r * p i) = c r
  change (∑ i, A i (e.symm (e r)) * p i) = c (e.symm (e r)) at hr
  simpa only [Equiv.symm_apply_apply] using hr

end

section
open Finset OnDemandDelivery.RouteElim
set_option maxHeartbeats 1000000
open Matrix Finset
open OnDemandDelivery.RouteElim

lemma route_dual_witness {R I P : Type} [Fintype R] [Fintype I] [Fintype P]
    (D : Data R I P) (φ : ℝ)
    (hφ : IsLeast (D.cost '' {θ | D.RF1Feasible θ}) φ) :
    ∃ (μ : P → ℝ) (μn : ℝ) (ν : I → ℝ),
      D.DualFeasible μ μn ν ∧ φ ≤ D.dualObjective μ μn ν := by
  classical
  let A : Matrix (P ⊕ (Unit ⊕ (I ⊕ R))) R ℝ :=
    Sum.elim D.β (Sum.elim (fun _ _ => 1)
      (Sum.elim (fun i r => -D.α i r) (fun j r => if r = j then -1 else 0)))
  let rhs : P ⊕ (Unit ⊕ (I ⊕ R)) → ℝ :=
    Sum.elim D.b (Sum.elim (fun _ => (D.Kbar : ℝ) - D.ζn)
      (Sum.elim (fun _ => -1) (fun _ => 0)))
  have hsystem (θ : R → ℝ) : A.mulVec θ ≤ rhs ↔ D.RF1Feasible θ := by
    constructor
    · intro h
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro p
        simpa [A, rhs, Matrix.mulVec, dotProduct] using h (Sum.inl p)
      · simpa [A, rhs, Matrix.mulVec, dotProduct] using h (Sum.inr (Sum.inl ()))
      · intro i
        have hi := h (Sum.inr (Sum.inr (Sum.inl i)))
        simpa [A, rhs, Matrix.mulVec, dotProduct] using hi
      · intro r
        have hr := h (Sum.inr (Sum.inr (Sum.inr r)))
        simpa [A, rhs, Matrix.mulVec, dotProduct] using hr
    · rintro ⟨hp, hn, hi, hr⟩ j
      rcases j with p | j
      · simpa [A, rhs, Matrix.mulVec, dotProduct] using hp p
      rcases j with u | j
      · simpa [A, rhs, Matrix.mulVec, dotProduct] using hn
      rcases j with i | r
      · simpa [A, rhs, Matrix.mulVec, dotProduct] using hi i
      · simpa [A, rhs, Matrix.mulVec, dotProduct] using hr r
  have hfeas : ∃ θ, A.mulVec θ ≤ rhs := by
    obtain ⟨θ, hθ, _⟩ := hφ.1
    exact ⟨θ, (hsystem θ).mpr hθ⟩
  have hvalid : ∀ θ, A.mulVec θ ≤ rhs → (-D.c) ⬝ᵥ θ ≤ -φ := by
    intro θ hθ
    have hc : φ ≤ D.cost θ := hφ.2 ⟨θ, (hsystem θ).mp hθ, rfl⟩
    simpa [Data.cost, dotProduct, mul_comm] using neg_le_neg hc
  obtain ⟨lam, hlam, hstat, hobj⟩ := route_farkas A rhs (-D.c) (-φ) hfeas hvalid
  let μ : P → ℝ := fun p => -lam (Sum.inl p)
  let μn : ℝ := -lam (Sum.inr (Sum.inl ()))
  let ν : I → ℝ := fun i => lam (Sum.inr (Sum.inr (Sum.inl i)))
  have hstationary (r : R) :
      (∑ p, D.β p r * lam (Sum.inl p)) + lam (Sum.inr (Sum.inl ())) -
        (∑ i, D.α i r * lam (Sum.inr (Sum.inr (Sum.inl i)))) -
        lam (Sum.inr (Sum.inr (Sum.inr r))) = -D.c r := by
    have hs := congrFun hstat r
    simpa [A, Matrix.mulVec, Matrix.transpose, Matrix.of_apply, dotProduct,
      Fintype.sum_sum_type, sub_eq_add_neg, add_assoc] using hs
  refine ⟨μ, μn, ν, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro p
    exact neg_nonpos.mpr (hlam (Sum.inl p))
  · exact neg_nonpos.mpr (hlam (Sum.inr (Sum.inl ())))
  · intro i
    exact hlam (Sum.inr (Sum.inr (Sum.inl i)))
  · intro r
    dsimp [μ, μn, ν]
    simp only [mul_neg, sum_neg_distrib]
    have hs := hstationary r
    have hl : (0 : ℝ) ≤ lam (Sum.inr (Sum.inr (Sum.inr r))) :=
      hlam (Sum.inr (Sum.inr (Sum.inr r)))
    linarith
  · simp [dotProduct, rhs, Fintype.sum_sum_type] at hobj
    dsimp [Data.dualObjective, μ, μn, ν]
    simp only [neg_mul, sum_neg_distrib]
    linarith

lemma route_strong {R I P : Type} [Fintype R] [Fintype I] [Fintype P]
    (D : Data R I P) (φ : ℝ)
    (hφ : IsLeast (D.cost '' {θ | D.RF1Feasible θ}) φ)
    (μ : P → ℝ) (μn : ℝ) (ν : I → ℝ) (hdual : D.DualOptimal μ μn ν) :
    D.dualObjective μ μn ν = φ := by
  obtain ⟨μ', μn', ν', hfeas, hobj⟩ := route_dual_witness D φ hφ
  have hlo := hobj.trans (hdual.2 μ' μn' ν' hfeas)
  obtain ⟨θ, hθ, hθφ⟩ := hφ.1
  have hhi := route_weak D θ hθ μ μn ν hdual.1
  rw [hθφ] at hhi
  exact le_antisymm hhi hlo

theorem solution {R I P : Type} [Fintype R] [Fintype I] [Fintype P]
    (D : Data R I P) (hD : D.Standing)
    (ub : ℝ) (hub : ∀ θ, D.SF1Optimal θ → D.cost θ ≤ ub)
    (φ : ℝ) (hφ : IsLeast (D.cost '' {θ | D.RF1Feasible θ}) φ)
    (μ : P → ℝ) (μn : ℝ) (ν : I → ℝ) (hdual : D.DualOptimal μ μn ν)
    (r : R) (h33 : ub - φ < D.reducedCost μ μn ν r) :
    ∀ θ, D.SF1Optimal θ → θ r = 0 := by
  exact route_root_using_value D hD ub hub φ μ μn ν hdual (route_strong D φ hφ μ μn ν hdual) r h33

end
