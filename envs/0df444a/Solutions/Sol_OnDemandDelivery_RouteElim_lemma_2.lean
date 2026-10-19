-- Prove2me | solution 1 for OnDemandDelivery.RouteElim.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-19T05:38:08.672715+00:00
-- url     : https://prove2.me/submissions/bc801293-ec4d-46a4-9496-25af5f48662e

import Mathlib
import Definitions.Def_OnDemandDelivery_RouteElim_Setting
import Theorems.Thm_LinearOptimization_farkas_inequality_form_fintype


open Finset OnDemandDelivery.RouteElim
set_option maxHeartbeats 1000000

lemma route_remove {R I P : Type} [Fintype R] [Fintype I] [Fintype P]
    (D : Data R I P) (hD : D.Standing) (r : R) (θ : R → ℝ)
    (hθ : D.SF1Feasible θ) (hr : θ r = 1) :
    ∃ θ', D.SF1rFeasible r θ' ∧ D.cost θ' = D.cost θ - D.c r := by
  classical
  let θ' : R → ℝ := fun s => if s = r then 0 else θ s
  have hbin : ∀ s, θ' s = 0 ∨ θ' s = 1 := by
    intro s
    by_cases hs : s = r
    · simp [θ', hs]
    · simpa [θ', hs] using hθ.2.2.2 s
  have hn : ∀ s, 0 ≤ θ' s := by
    intro s
    rcases hbin s with h | h <;> simp [h]
  have hsum (f : R → ℝ) : (∑ s, f s * θ' s) = (∑ s, f s * θ s) - f r := by
    calc
      _ = ∑ s, (f s * θ s - if s = r then f r else 0) := by
        apply sum_congr rfl
        intro s _
        by_cases hs : s = r
        · simp [θ', hs, hr]
        · simp [θ', hs]
      _ = _ := by rw [sum_sub_distrib]; simp
  have hsupport : ∀ s, ¬ D.InRr r s → θ' s = 0 := by
    intro s hns
    by_contra hne
    have hs1 : θ' s = 1 := (hbin s).resolve_left hne
    obtain ⟨i, hi⟩ := not_forall.mp hns
    have hi' : D.α i s ≠ 0 ∧ D.α i r ≠ 0 := by simpa only [_root_.not_imp] using hi
    have has : D.α i s = 1 := (hD.1 i s).resolve_left hi'.1
    have har : D.α i r = 1 := (hD.1 i r).resolve_left hi'.2
    have hz : (∑ t, D.α i t * θ' t) = 0 := by rw [hsum, hθ.2.2.1 i, har]; norm_num
    have ht : D.α i s * θ' s ≤ ∑ t, D.α i t * θ' t := by
      apply Finset.single_le_sum (s := univ) (f := fun t => D.α i t * θ' t)
      · intro t _
        have hα : 0 ≤ D.α i t := by rcases hD.1 i t with h | h <;> simp [h]
        exact mul_nonneg hα (hn t)
      · exact mem_univ _
    rw [hz, has, hs1] at ht
    norm_num at ht
  refine ⟨θ', ⟨hsupport, ?_, ?_, ?_, hbin⟩, ?_⟩
  · intro p
    rw [hsum]
    exact sub_le_sub_right (hθ.1 p) _
  · have hh := hsum (fun _ => 1)
    simp only [one_mul] at hh
    rw [hh]
    linarith [hθ.2.1]
  · intro i hi
    rw [hsum, hθ.2.2.1 i, hi, sub_zero]
  · simpa only [Data.cost, mul_comm] using hsum D.c

lemma route_eq74 {R I P : Type} [Fintype R] [Fintype I] [Fintype P]
    (D : Data R I P) (hD : D.Standing)
    (ub : ℝ) (hub : ∀ θ, D.SF1Optimal θ → D.cost θ ≤ ub)
    (r : R) (h74 : (ub : EReal) < (D.c r : EReal) + D.phiSF1r r) :
    ∀ θ, D.SF1Optimal θ → θ r = 0 := by
  intro θ hθ
  rcases hθ.1.2.2.2 r with hr | hr
  · exact hr
  obtain ⟨θ', hf, hc⟩ := route_remove D hD r θ hθ.1 hr
  have hphi : D.phiSF1r r ≤ (D.cost θ' : EReal) := sInf_le ⟨θ', hf, rfl⟩
  have hlt := h74.trans_le (add_le_add le_rfl hphi)
  have heq : (D.c r : EReal) + (D.cost θ' : EReal) = (D.cost θ : EReal) := by
    rw [← EReal.coe_add]
    congr 1
    linarith
  rw [heq] at hlt
  have hle : (D.cost θ : EReal) ≤ (ub : EReal) := by exact_mod_cast hub θ hθ
  exact False.elim ((not_lt_of_ge hle) hlt)

lemma route_restrict_dual {R I P : Type} [Fintype R] [Fintype I] [Fintype P]
    (D : Data R I P) (μ : P → ℝ) (μn : ℝ) (ν : I → ℝ)
    (hdual : D.DualFeasible μ μn ν) (r : R) : D.RF1rDualFeasible r μ μn ν := by
  classical
  refine ⟨hdual.1, hdual.2.1, ?_⟩
  intro s hs
  have heq : (∑ i ∈ univ.filter (fun i => D.α i r = 0), D.α i s * ν i) = ∑ i, D.α i s * ν i := by
    rw [sum_filter]
    apply sum_congr rfl
    intro i _
    by_cases hi : D.α i r = 0
    · simp [hi]
    · have hiz : D.α i s = 0 := by by_contra h; exact hi (hs i h)
      simp [hi, hiz]
  rw [heq]
  exact hdual.2.2.2 s

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

lemma route_restricted_weak {R I P : Type} [Fintype R] [Fintype I] [Fintype P]
    (D : Data R I P) (r : R) (μ : P → ℝ) (μn : ℝ) (ν : I → ℝ)
    (hd : D.RF1rDualFeasible r μ μn ν) (θ : R → ℝ) (hθ : D.RF1rFeasible r θ) :
    D.rf1rBound r μ μn ν ≤ D.cost θ := by
  classical
  let S := univ.filter (fun i => D.α i r = 0)
  have hcost : (∑ s, θ s * ((∑ i ∈ S, D.α i s * ν i) + (∑ p, D.β p s * μ p) + μn)) ≤ D.cost θ := by
    apply sum_le_sum
    intro s _
    by_cases hs : D.InRr r s
    · exact mul_le_mul_of_nonneg_left (hd.2.2 s hs) (hθ.2.2.2.2 s)
    · simp [hθ.1 s hs]
  rw [route_sum_identity] at hcost
  have hcov : (∑ i ∈ S, ν i * (∑ s, D.α i s * θ s)) = ∑ i ∈ S, ν i := by
    apply sum_congr rfl
    intro i hi
    rw [hθ.2.2.2.1 i (mem_filter.mp hi).2, mul_one]
  rw [hcov] at hcost
  have hp : (∑ p, μ p * (D.b p - D.β p r)) ≤ ∑ p, μ p * (∑ s, D.β p s * θ s) := by
    apply sum_le_sum
    intro p _
    exact mul_le_mul_of_nonpos_left (hθ.2.1 p) (hd.1 p)
  have hn := mul_le_mul_of_nonpos_left hθ.2.2.1 hd.2.1
  have hid : (∑ p, μ p * (D.b p - D.β p r)) = (∑ p, μ p * D.b p) - ∑ p, D.β p r * μ p := by
    simp_rw [mul_sub]
    rw [sum_sub_distrib]
    congr 1
    apply sum_congr rfl
    intro p _
    ring
  rw [hid] at hp
  dsimp [Data.rf1rBound]
  dsimp [S] at hcost
  linarith

lemma route_dual_bound {R I P : Type} [Fintype R] [Fintype I] [Fintype P]
    (D : Data R I P) (hD : D.Standing)
    (μ : P → ℝ) (μn : ℝ) (ν : I → ℝ) (hdual : D.DualFeasible μ μn ν) (r : R) :
    D.RF1rDualFeasible r μ μn ν ∧
      (∀ θ', D.RF1rFeasible r θ' → D.rf1rBound r μ μn ν ≤ D.cost θ') ∧
      ((D.rf1rBound r μ μn ν : ℝ) : EReal) ≤ D.phiSF1r r := by
  have hd := route_restrict_dual D μ μn ν hdual r
  refine ⟨hd, route_restricted_weak D r μ μn ν hd, ?_⟩
  apply le_sInf
  rintro v ⟨θ, hθ, rfl⟩
  have hf : D.RF1rFeasible r θ := by
    refine ⟨hθ.1, hθ.2.1, hθ.2.2.1, hθ.2.2.2.1, ?_⟩
    intro s
    rcases hθ.2.2.2.2 s with h | h <;> simp [h]
  change (D.rf1rBound r μ μn ν : EReal) ≤ (D.cost θ : EReal)
  exact_mod_cast route_restricted_weak D r μ μn ν hd θ hf

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
  have hbound := (route_dual_bound D hD μ μn ν hdual.1 r).2.2
  apply route_eq74 D hD ub hub r
  have he : (ub : EReal) < ((D.c r + D.rf1rBound r μ μn ν : ℝ) : EReal) := by exact_mod_cast hreal
  rw [EReal.coe_add] at he
  exact he.trans_le (add_le_add le_rfl hbound)


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
