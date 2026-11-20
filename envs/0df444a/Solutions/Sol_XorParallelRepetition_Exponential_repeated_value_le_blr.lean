-- Prove2me | solution 1 for XorParallelRepetition.Exponential.repeated_value_le_blr
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:28:44.753688+00:00
-- url     : https://prove2.me/submissions/98af65e2-e532-4ce9-9d46-0590204a7dca

import Mathlib
import Definitions.Def_XorParallelRepetition_Exponential_XorGames
import Definitions.Def_XorParallelRepetition_Exponential_BLR
universe u

section
set_option autoImplicit false

open scoped ENNReal

namespace XorParallelRepetition.Dev.BlrRep

open XorParallelRepetition.Exponential

theorem iidPMF_map {α β : Type*} (μ : PMF α) (f : α → β) :
    ∀ n : ℕ, iidPMF (μ.map f) n = (iidPMF μ n).map (fun s => f ∘ s)
  | 0 => by
    simp only [iidPMF, PMF.pure_map]
    congr 1
    funext j
    exact j.elim0
  | n + 1 => by
    simp only [iidPMF]
    rw [iidPMF_map μ f n, PMF.bind_map, PMF.map_bind]
    congr 1
    funext a
    simp only [Function.comp_apply, PMF.map_comp]
    congr 1
    funext s
    simp [Fin.comp_cons]

theorem winProb_le_one {ι : Type} (G : Game ι) (S : G.Strategy) : G.winProb S ≤ 1 := by
  unfold Game.winProb
  calc G.law.toOuterMeasure _ ≤ G.law.toOuterMeasure Set.univ := PMF.toOuterMeasure_mono _ (fun _ _ => trivial)
    _ = 1 := by rw [PMF.toOuterMeasure_apply_eq_one_iff]; exact Set.subset_univ _

end XorParallelRepetition.Dev.BlrRep

namespace XorParallelRepetition.Exponential


open XorParallelRepetition.Dev.BlrRep in
theorem chk_repeated_value_le_blr {p : ℕ} [Fact p.Prime] {ι : Type} [Fintype ι] [DecidableEq ι]
    (Ψ : XorGame.{u} p ι) (n : ℕ) :
    Ψ.repVal n ≤ Ψ.blr.repVal n := by
  -- the triple law `(x, γ, α)`
  let τ : PMF ((∀ i, Ψ.Q i) × ZMod p × (ι → ZMod p)) :=
    Ψ.μ.bind fun x => (PMF.uniformOfFintype (ZMod p)).bind fun γ =>
      (PMF.uniformOfFintype (ι → ZMod p)).map fun α => (x, γ, α)
  let g : (∀ i, Ψ.Q i) × ZMod p × (ι → ZMod p) → (∀ s, Ψ.blr.Q s) × ZMod p := fun z => Ψ.blrChallenge z.1 z.2.1 z.2.2
  let k : (∀ i, Ψ.Q i) × ZMod p × (ι → ZMod p) → (∀ i, Ψ.toGeneralized.Q i) × ZMod p :=
    fun z => (z.1, Ψ.t z.1)
  let g' : (∀ i, Ψ.Q i) × ZMod p × (ι → ZMod p) → (∀ s : ι × Bool, Ψ.Q s.1 × ZMod p) × ZMod p :=
    fun z => Ψ.blrChallenge z.1 z.2.1 z.2.2
  have hg' : Ψ.μ.bind (fun x => (PMF.uniformOfFintype (ZMod p)).bind fun γ =>
      (PMF.uniformOfFintype (ι → ZMod p)).map fun α => Ψ.blrChallenge x γ α) = τ.map g' := by
    simp only [τ, PMF.map_bind, PMF.map_comp]
    rfl
  have hg : Ψ.blr.μ = τ.map g := hg'
  let k' : (∀ i, Ψ.Q i) × ZMod p × (ι → ZMod p) → (∀ i, Ψ.Q i) × ZMod p :=
    fun z => (z.1, Ψ.t z.1)
  have hk' : Ψ.μ.map (fun x => (x, Ψ.t x)) = τ.map k' := by
    simp only [τ, PMF.map_bind, PMF.map_comp]
    have : ∀ x : ∀ i, Ψ.Q i, ((PMF.uniformOfFintype (ZMod p)).bind fun γ =>
        (PMF.uniformOfFintype (ι → ZMod p)).map (k' ∘ fun α => (x, γ, α))) = PMF.pure (x, Ψ.t x) := by
      intro x
      have h1 : ∀ γ : ZMod p, (PMF.uniformOfFintype (ι → ZMod p)).map (k' ∘ fun α => (x, γ, α))
          = PMF.pure (x, Ψ.t x) := fun γ => by
        rw [show (k' ∘ fun α => (x, γ, α)) = Function.const (ι → ZMod p) (x, Ψ.t x) from rfl]
        exact PMF.map_const _ _
      simp only [h1]
      exact PMF.bind_const _ _
    simp only [this]
    rfl
  have hk : Ψ.toGeneralized.μ = τ.map k := hk'
  unfold XorGame.repVal GeneralizedXorGame.repVal Game.val
  have hfin : (⨆ S : (Ψ.blr.toGame.rep n).Strategy, (Ψ.blr.toGame.rep n).winProb S) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (iSup_le fun S => winProb_le_one _ S)
  refine ENNReal.toReal_mono hfin (iSup_le fun A => ?_)
  -- the strategy for the BLR game
  let A' : ∀ i, (Fin n → Ψ.Q i) → Fin n → ZMod p := A
  let B : ∀ q : ι × Bool, (Fin n → Ψ.Q q.1 × ZMod p) → Fin n → ZMod p := fun s y j =>
    if s.2 then (y j).2 * A' s.1 (fun j => (y j).1) j else -((y j).2 * A' s.1 (fun j => (y j).1) j)
  refine le_iSup_of_le (B : (Ψ.blr.toGame.rep n).Strategy) ?_
  have e1 : (Ψ.toGeneralized.toGame.rep n).winProb A = (iidPMF Ψ.toGeneralized.μ n).toOuterMeasure
      {s : Fin n → (∀ i, Ψ.toGeneralized.Q i) × ZMod p | ∀ j, (∑ i, A' i (fun j => (s j).1 i) j : ZMod p) = (s j).2} := by
    unfold Game.winProb
    exact PMF.toOuterMeasure_map_apply _ _ _
  have e2 : (Ψ.blr.toGame.rep n).winProb (B : (Ψ.blr.toGame.rep n).Strategy) = (iidPMF Ψ.blr.μ n).toOuterMeasure
      {s : Fin n → (∀ q : ι × Bool, Ψ.Q q.1 × ZMod p) × ZMod p |
        ∀ j, ∑ i, (B i (fun j => (s j).1 i) j : ZMod p) = (s j).2} := by
    unfold Game.winProb
    exact PMF.toOuterMeasure_map_apply _ _ _
  rw [e1, e2, hg, hk, iidPMF_map, iidPMF_map, PMF.toOuterMeasure_map_apply,
    PMF.toOuterMeasure_map_apply]
  apply PMF.toOuterMeasure_mono
  intro z hz j
  have hj : (∑ i, A' i (fun j => (z j).1 i) j : ZMod p) = Ψ.t (z j).1 := hz.1 j
  show ∑ q : ι × Bool, B q (fun j' => ((z j').1 q.1,
      if q.2 then (z j').2.2 q.1 + (z j').2.1 else (z j').2.2 q.1)) j = (z j).2.1 * Ψ.t (z j).1
  rw [Fintype.sum_prod_type]
  simp only [B, Fintype.sum_bool, if_true, Bool.false_eq_true, if_false]
  have : ∀ i, (z j).2.2 i + (z j).2.1 + -((z j).2.2 i) = (z j).2.1 := fun i => by ring
  simp_rw [neg_mul_eq_neg_mul, ← add_mul, this, ← Finset.mul_sum, hj]

end XorParallelRepetition.Exponential
end

theorem solution : type_of% @XorParallelRepetition.Exponential.chk_repeated_value_le_blr := @XorParallelRepetition.Exponential.chk_repeated_value_le_blr
