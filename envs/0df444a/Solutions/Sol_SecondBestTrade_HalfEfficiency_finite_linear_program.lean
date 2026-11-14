-- Prove2me | solution 1 for SecondBestTrade.HalfEfficiency.finite_linear_program
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-13T15:27:54.214106+00:00
-- url     : https://prove2.me/submissions/9b940247-39d1-480f-bf0a-4a95c0b2fb1b

import Definitions.Def_SecondBestTrade_HalfEfficiency_Mechanisms

open scoped BigOperators
open SecondBestTrade.HalfEfficiency

noncomputable section

theorem secondBestTradeVariableCard (N : Market) :
    Fintype.card (Variable N) = (N.ne + N.nb + N.ns) * Fintype.card (Profile N) := by
  simp only [Variable, Agent, Trade, Fintype.card_prod, Fintype.card_sum, Fintype.card_fin]
  ring

private theorem emptyFeasible (N : Market) : (∅ : Finset (Trade N)) ∈ N.family := by
  obtain ⟨X,hX⟩ := N.family_nonempty
  exact N.downward X hX ∅ (Finset.empty_subset X)

theorem secondBestTradeZeroFeasible (N : Market) : programFeasible N (zeroSigned N) := by
  refine ⟨fun v => ?_, ?_, ?_⟩
  · apply subset_convexHull
    refine ⟨∅, emptyFeasible N, ?_⟩
    ext e
    simp [zeroSigned, indicator]
  · simp [WBB, zeroSigned, expect]
  · intro a t r
    cases a <;> cases r <;>
      simp [reportUtility, U, expect, valueUtility, zeroSigned, nullAllocation, nullTransfer]

private theorem surplus_le_max (N : Market) (q w : Trade N → ℝ) (hq : q ∈ allocationPolytope N) :
    (∑ e, q e * w e) ≤ maxSurplus N w := by
  classical
  let l : (Trade N → ℝ) → ℝ := fun x => ∑ e, x e * w e
  have lin : IsLinearMap ℝ l := by
    constructor
    · intro x y
      simp [l, add_mul, Finset.sum_add_distrib]
    · intro c x
      simp [l, mul_assoc, Finset.mul_sum]
  apply (convexHull_min (t := {x | l x ≤ maxSurplus N w}) ?_ (convex_halfSpace_le lin _)) hq
  rintro x ⟨X,hX,rfl⟩
  change (∑ e, indicator N X e * w e) ≤ _
  have eq : (∑ e, indicator N X e * w e) = ∑ e ∈ X, w e := by
    simp [indicator, ite_mul, Finset.sum_ite_mem]
  rw [eq]
  exact Finset.le_sup' (fun X => ∑ e ∈ X, w e) hX

theorem secondBestTradeGainsBound (N : Market) (m : SignedMechanism N)
    (h : programFeasible N m) : GFT N m.q ≤ FB N := by
  apply Finset.sum_le_sum
  intro v _
  exact mul_le_mul_of_nonneg_left (surplus_le_max N (m.q v) (gains N v) (h.1 v))
    (Finset.prod_nonneg (fun a _ => (N.mass_pos a (v a)).le))

namespace TradePolyhedra
open Set

variable {E : Type} [AddCommGroup E] [Module ℝ E]

/-- A system of finitely many closed affine half spaces. -/
def Presented (P : E → Prop) : Prop :=
  ∃ (I : Type) (_ : Fintype I) (A : I → E →ₗ[ℝ] ℝ) (b : I → ℝ),
    ∀ x, P x ↔ ∀ i, A i x ≤ b i

private theorem bounds {L U : Type} [Fintype L] [Fintype U]
    (l : L → ℝ) (u : U → ℝ) :
    (∃ x : ℝ, (∀ i, l i ≤ x) ∧ (∀ j, x ≤ u j)) ↔ ∀ i j, l i ≤ u j := by
  classical
  constructor
  · rintro ⟨x,h,k⟩ i j
    exact (h i).trans (k j)
  · intro h
    cases isEmpty_or_nonempty L with
    | inl he =>
      cases isEmpty_or_nonempty U with
      | inl hu => exact ⟨0,isEmptyElim,isEmptyElim⟩
      | inr hu =>
        obtain ⟨j,_,hj⟩ := Finset.exists_min_image (Finset.univ : Finset U) u Finset.univ_nonempty
        exact ⟨u j,isEmptyElim,fun j' => hj j' (Finset.mem_univ _)⟩
    | inr hl =>
      obtain ⟨i,_,hi⟩ := Finset.exists_max_image (Finset.univ : Finset L) l Finset.univ_nonempty
      exact ⟨l i,fun i' => hi i' (Finset.mem_univ _),h i⟩

/-- Eliminate one real variable by comparing every lower bound to every upper bound. -/
theorem projectScalar {P : ℝ × E → Prop} (hp : Presented P) :
    Presented (fun x => ∃ t, P (t,x)) := by
  classical
  obtain ⟨I,inst,A,b,eq⟩ := hp
  let c := fun i => A i (1,0)
  let F := fun i => (A i).comp (LinearMap.inr ℝ ℝ E)
  have dec (i) (t : ℝ) (x : E) : A i (t,x) = c i * t + F i x := by
    have h : (t,x) = t • (1,0) + (0,x) := by simp
    rw [h, map_add, map_smul]
    change t * c i + F i x = _
    ring
  let Z := {i : I // c i = 0}
  let L := {i : I // c i < 0}
  let U := {i : I // 0 < c i}
  let A' : Z ⊕ L × U → E →ₗ[ℝ] ℝ := Sum.elim (fun i => F i.1) (fun p =>
    (c p.2.1)⁻¹ • F p.2.1 - (c p.1.1)⁻¹ • F p.1.1)
  let b' : Z ⊕ L × U → ℝ := Sum.elim (fun i => b i.1) (fun p =>
    b p.2.1 / c p.2.1 - b p.1.1 / c p.1.1)
  refine ⟨Z ⊕ L × U,inferInstance,A',b',fun x => ?_⟩
  let l := fun i : L => (b i.1 - F i.1 x) / c i.1
  let u := fun i : U => (b i.1 - F i.1 x) / c i.1
  have pair (i : L) (j : U) : A' (.inr (i,j)) x ≤ b' (.inr (i,j)) ↔ l i ≤ u j := by
    change (c j.1)⁻¹ * F j.1 x - (c i.1)⁻¹ * F i.1 x ≤ b j.1 / c j.1 - b i.1 / c i.1 ↔ _
    dsimp only [l,u]
    simp only [sub_div, div_eq_mul_inv]
    constructor <;> intro h <;> linarith only [h]
  constructor
  · rintro ⟨t,ht⟩ ij
    have row (i : I) := (eq _).mp ht i
    simp_rw [dec] at row
    cases ij with
    | inl i =>
      have h := row i.1
      change F i.1 x ≤ b i.1
      simpa only [i.property,zero_mul,zero_add] using h
    | inr p =>
      obtain ⟨i,j⟩ := p
      apply (pair i j).mpr
      exact le_trans (b := t) ((div_le_iff_of_neg i.property).mpr (by linarith [row i.1]))
        ((le_div_iff₀ j.property).mpr (by linarith [row j.1]))
  · intro h
    have hc := (bounds l u).mpr (fun i j => (pair i j).mp (h (.inr (i,j))))
    obtain ⟨t,hl,hu⟩ := hc
    refine ⟨t,(eq _).mpr (fun i => ?_)⟩
    rw [dec]
    rcases lt_trichotomy (c i) 0 with hi|hi|hi
    · have hr := (div_le_iff_of_neg hi).mp (hl ⟨i,hi⟩)
      linarith
    · simpa [hi,A',b'] using h (.inl ⟨i,hi⟩)
    · have hr := (le_div_iff₀ hi).mp (hu ⟨i,hi⟩)
      linarith

theorem preimage {F : Type} [AddCommGroup F] [Module ℝ F] {P : E → Prop}
    (h : Presented P) (f : F →ₗ[ℝ] E) : Presented (fun x => P (f x)) := by
  obtain ⟨I,inst,A,b,eq⟩ := h
  exact ⟨I,inst,fun i => (A i).comp f,b,fun x => eq (f x)⟩

theorem congr {P Q : E → Prop} (h : Presented P) (eq : ∀ x, P x ↔ Q x) : Presented Q := by
  obtain ⟨I,inst,A,b,rows⟩ := h
  exact ⟨I,inst,A,b,fun x => (eq x).symm.trans (rows x)⟩

theorem projectFin {n : ℕ} {P : (Fin n → ℝ) × E → Prop} (h : Presented P) :
    Presented (fun x => ∃ t, P (t,x)) := by
  induction n generalizing E with
  | zero =>
    have h' := preimage h (LinearMap.inr ℝ (Fin 0 → ℝ) E)
    apply congr h'
    intro x
    constructor
    · exact fun hp => ⟨0,hp⟩
    · rintro ⟨t,ht⟩
      change P (0,x)
      simpa only [Subsingleton.elim t 0] using ht
  | succ n ih =>
    let f : ℝ × ((Fin n → ℝ) × E) →ₗ[ℝ] (Fin (n+1) → ℝ) × E :=
      (LinearMap.vecCons (LinearMap.fst ℝ _ _) ((LinearMap.fst ℝ _ _).comp (LinearMap.snd ℝ _ _))).prod
        ((LinearMap.snd ℝ _ _).comp (LinearMap.snd ℝ _ _))
    have h' := ih (projectScalar (preimage h f))
    apply congr h'
    intro x
    constructor
    · rintro ⟨t,s,ht⟩
      exact ⟨_,ht⟩
    · rintro ⟨t,ht⟩
      refine ⟨Fin.tail t,t 0,?_⟩
      change P (Fin.cons (t 0) (Fin.tail t),x)
      simpa only [Fin.cons_self_tail] using ht

theorem project {J : Type} [Fintype J] {P : (J → ℝ) × E → Prop} (h : Presented P) :
    Presented (fun x => ∃ t, P (t,x)) := by
  classical
  let e := Fintype.equivFin J
  let f : (Fin (Fintype.card J) → ℝ) × E →ₗ[ℝ] (J → ℝ) × E :=
    { toFun := fun p => (p.1 ∘ e,p.2), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  apply congr (projectFin (preimage h f))
  intro x
  constructor
  · rintro ⟨t,ht⟩
    exact ⟨_,ht⟩
  · rintro ⟨t,ht⟩
    refine ⟨t ∘ e.symm,?_⟩
    change P ((fun j => t (e.symm (e j))),x)
    simpa only [Equiv.symm_apply_apply] using ht

theorem halfspace (f : E →ₗ[ℝ] ℝ) (b : ℝ) : Presented (fun x => f x ≤ b) :=
  ⟨Unit,inferInstance,fun _ => f,fun _ => b,fun _ => ⟨fun h _ => h,fun h => h ()⟩⟩

theorem intersection {P Q : E → Prop} (hp : Presented P) (hq : Presented Q) :
    Presented (fun x => P x ∧ Q x) := by
  obtain ⟨I,_,A,b,p⟩ := hp
  obtain ⟨J,_,B,c,q⟩ := hq
  refine ⟨I ⊕ J,inferInstance,Sum.elim A B,Sum.elim b c,fun x => ?_⟩
  change (P x ∧ Q x) ↔ _
  rw [p,q,Sum.forall]
  rfl

theorem equality (f : E →ₗ[ℝ] ℝ) (b : ℝ) : Presented (fun x => f x = b) := by
  apply congr (intersection (halfspace f b) (halfspace (-f) (-b)))
  intro x
  simp [le_antisymm_iff]

theorem forallFinite {I : Type} [Fintype I] {P : I → E → Prop} (h : ∀ i, Presented (P i)) :
    Presented (fun x => ∀ i, P i x) := by
  classical
  choose J inst A b eq using h
  letI : ∀ i, Fintype (J i) := inst
  refine ⟨Σ i, J i,inferInstance,fun ij => A ij.1 ij.2,fun ij => b ij.1 ij.2,fun x => ?_⟩
  simp only [eq,Sigma.forall]

theorem isClosed {P : ℝ → Prop} (h : Presented P) : IsClosed {x | P x} := by
  obtain ⟨I,_,A,b,eq⟩ := h
  have setEq : {x | P x} = ⋂ i, {x | A i x ≤ b i} := by ext x; simpa only [Set.mem_setOf_eq,Set.mem_iInter] using eq x
  rw [setEq]
  exact isClosed_iInter (fun i => isClosed_le (A i).continuous_of_finiteDimensional continuous_const)

theorem attain {J : Type} [Fintype J] {P : (J → ℝ) → Prop} (h : Presented P)
    (f : (J → ℝ) →ₗ[ℝ] ℝ) (hn : ∃ x, P x) (hb : BddAbove {r | ∃ x, P x ∧ r = f x}) :
    ∃ x, P x ∧ f x = sSup {r | ∃ x, P x ∧ r = f x} := by
  let g : ((J → ℝ) × ℝ) →ₗ[ℝ] ℝ := (LinearMap.snd ℝ _ _) - f.comp (LinearMap.fst ℝ _ _)
  have proj := project (intersection (preimage h (LinearMap.fst ℝ _ ℝ)) (equality g 0))
  have pres : Presented (fun r => ∃ x, P x ∧ r = f x) := by
    apply congr proj
    intro r
    exact exists_congr (fun x => by change P x ∧ r - f x = 0 ↔ _; rw [sub_eq_zero])
  obtain ⟨x,hx⟩ := hn
  obtain ⟨y,hy,eq⟩ := (isClosed pres).csSup_mem ⟨f x,x,hx,rfl⟩ hb
  exact ⟨y,hy,eq.symm⟩

/-- Finite vertex descriptions have finite inequality presentations in the original
coordinates, by eliminating the convex-combination coefficients. -/
theorem finiteHull {J : Type} [Fintype J] (V : Finset (J → ℝ)) :
    Presented (fun x => x ∈ convexHull ℝ (V : Set (J → ℝ))) := by
  classical
  let W := (↑V : Type) → ℝ
  let eval : ∀ i : ↑V, (W × (J → ℝ)) →ₗ[ℝ] ℝ := fun i =>
    { toFun := fun p => p.1 i, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let get : ∀ j : J, (W × (J → ℝ)) →ₗ[ℝ] ℝ := fun j =>
    { toFun := fun p => p.2 j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let one : W × (J → ℝ) →ₗ[ℝ] ℝ := ∑ i, eval i
  let combo (j : J) : W × (J → ℝ) →ₗ[ℝ] ℝ := ∑ i : ↑V, (i.1 j) • eval i
  have hp := project (intersection (forallFinite (fun i : ↑V => halfspace (-eval i) 0))
    (intersection (equality one 1) (forallFinite (fun j : J => equality (combo j - get j) 0))))
  apply congr hp
  intro x
  constructor
  · rintro ⟨w,hn,hs,he⟩
    apply mem_convexHull_of_exists_fintype w (fun i : ↑V => i.1)
    · intro i
      simpa [eval] using hn i
    · simpa [one,eval,LinearMap.sum_apply] using hs
    · exact fun i => i.2
    · ext j
      have h := he j
      simp only [combo,get,eval,LinearMap.sub_apply,LinearMap.sum_apply,LinearMap.smul_apply,
        LinearMap.coe_mk,AddHom.coe_mk,smul_eq_mul,sub_eq_zero] at h
      simpa [Finset.sum_apply,Pi.smul_apply,mul_comm] using h
  · intro hx
    obtain ⟨w,hn,hs,he⟩ := Finset.mem_convexHull'.mp hx
    refine ⟨fun i => w i.1,fun i => ?_,?_,fun j => ?_⟩
    · simpa [eval] using hn i.1 i.2
    · simpa [one,eval,LinearMap.sum_apply,Finset.sum_attach] using hs
    · have h := congrFun he j
      simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] at h
      rw [← Finset.sum_attach V (fun y => w y * y j)] at h
      simpa [combo,eval,get,LinearMap.sum_apply,sub_eq_zero,mul_comm] using h

end TradePolyhedra


private def xRead (N : Market) (v : Profile N) : LPVector N →ₗ[ℝ] (Trade N → ℝ) where
  toFun := fun u e => u (v,.inl e)
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

private def tRead (N : Market) (a : Agent N) (v : Profile N) : LPVector N →ₗ[ℝ] ℝ :=
  LinearMap.proj (v,.inr a)

private def expectedRow (N : Market) (f : Profile N → (LPVector N →ₗ[ℝ] ℝ)) :
    LPVector N →ₗ[ℝ] ℝ := ∑ v, prior N v • f v

private theorem expectedRow_apply (N : Market) (f : Profile N → (LPVector N →ₗ[ℝ] ℝ))
    (u : LPVector N) : expectedRow N f u = expect N (fun v => f v u) := by
  simp only [expectedRow,expect,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul]

private def vRow (N : Market) (a : Agent N) (t : Ty N a) (v : Profile N) : LPVector N →ₗ[ℝ] ℝ :=
  Sum.elim (fun _ => ∑ e, coord N a t e • (LinearMap.proj (v,.inl e) : LPVector N →ₗ[ℝ] ℝ))
    (fun _ => -(∑ e, coord N a t e • (LinearMap.proj (v,.inl e) : LPVector N →ₗ[ℝ] ℝ))) a

private theorem vRow_apply (N : Market) (a : Agent N) (t : Ty N a) (v : Profile N) (u : LPVector N) :
    vRow N a t v u = valueUtility N a t ((decode N u).q v) := by
  cases a <;> simp [vRow,valueUtility,decode,LinearMap.sum_apply]

private def uRow (N : Market) (a : Agent N) (t r : Ty N a) : LPVector N →ₗ[ℝ] ℝ :=
  expectedRow N (fun v => vRow N a t (overwrite N v a r) - tRead N a (overwrite N v a r))

private theorem uRow_apply (N : Market) (a : Agent N) (t r : Ty N a) (u : LPVector N) :
    uRow N a t r u = U N (decode N u) a t r := by
  simp only [uRow,expectedRow_apply,LinearMap.sub_apply,vRow_apply,U,tRead,LinearMap.proj_apply,decode]

private def rRow (N : Market) (a : Agent N) (t : Ty N a) (r : Option (Ty N a)) : LPVector N →ₗ[ℝ] ℝ :=
  r.elim 0 (uRow N a t)

private theorem rRow_apply (N : Market) (a : Agent N) (t : Ty N a) (r : Option (Ty N a)) (u : LPVector N) :
    rRow N a t r u = reportUtility N (decode N u) a t r := by
  cases r with
  | none => cases a <;> simp [rRow,reportUtility,valueUtility,nullAllocation,nullTransfer]
  | some r => exact uRow_apply N a t r u

private def gainRow (N : Market) : LPVector N →ₗ[ℝ] ℝ :=
  expectedRow N (fun v => ∑ e, gains N v e • (LinearMap.proj (v,.inl e) : LPVector N →ₗ[ℝ] ℝ))

private theorem gainRow_apply (N : Market) (u : LPVector N) : gainRow N u = GFT N (decode N u).q := by
  unfold gainRow GFT
  rw [expectedRow_apply]
  simp only [LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.proj_apply,smul_eq_mul,decode]
  simp only [mul_comm]

private theorem programPresented (N : Market) : TradePolyhedra.Presented (fun u => programFeasible N (decode N u)) := by
  classical
  let V := N.family.image (indicator N)
  have hull : TradePolyhedra.Presented (fun y => y ∈ allocationPolytope N) := by
    have h : (V : Set (Trade N → ℝ)) = {y | ∃ X ∈ N.family, y = indicator N X} := by
      ext y
      simp [V,eq_comm]
    simpa only [h,allocationPolytope] using TradePolyhedra.finiteHull V
  have alloc := TradePolyhedra.forallFinite (fun v : Profile N => TradePolyhedra.preimage hull (xRead N v))
  let budget := expectedRow N (fun v => ∑ a, tRead N a v)
  have ic := TradePolyhedra.forallFinite (fun a : Agent N => TradePolyhedra.forallFinite (fun t : Ty N a =>
    TradePolyhedra.forallFinite (fun r : Option (Ty N a) => TradePolyhedra.halfspace (rRow N a t r - uRow N a t t) 0)))
  apply TradePolyhedra.congr (TradePolyhedra.intersection alloc (TradePolyhedra.intersection (TradePolyhedra.halfspace (-budget) 0) ic))
  intro u
  change (feasible N (decode N u).q ∧ (-budget) u ≤ 0 ∧
    ∀ a t r, (rRow N a t r - uRow N a t t) u ≤ 0) ↔ _
  simp only [programFeasible,WBB,budget,LinearMap.neg_apply,expectedRow_apply,LinearMap.sum_apply,
    tRead,LinearMap.proj_apply,neg_nonpos,LinearMap.sub_apply,rRow_apply,uRow_apply,sub_nonpos,decode]

private def encodeTrade (N : Market) (m : SignedMechanism N) : LPVector N :=
  fun w => Sum.elim (fun e => m.q w.1 e) (fun a => m.t a w.1) w.2

private theorem decode_encode (N : Market) (m : SignedMechanism N) : decode N (encodeTrade N m) = m := by
  cases m
  rfl

theorem solution (N : Market) :
    finiteLPPresentation N ∧
    Fintype.card (Variable N) = (N.ne + N.nb + N.ns) * Fintype.card (Profile N) ∧
    programFeasible N (zeroSigned N) ∧
    (∀ m : SignedMechanism N, programFeasible N m → GFT N m.q ≤ FB N) ∧
    ∃ m : SignedMechanism N, programFeasible N m ∧ GFT N m.q = OPT N := by
  classical
  have presentation := programPresented N
  refine ⟨?_, secondBestTradeVariableCard N, secondBestTradeZeroFeasible N, secondBestTradeGainsBound N, ?_⟩
  · obtain ⟨I,inst,A,b,h⟩ := presentation
    let e := Fintype.equivFin I
    refine ⟨Fintype.card I, fun j => A (e.symm j), fun j => b (e.symm j), gainRow N, ?_, gainRow_apply N⟩
    intro u
    refine (h u).trans ?_
    exact ⟨fun h j => h _,fun h i => by simpa only [Equiv.symm_apply_apply] using h (e i)⟩
  · have ne : ∃ u, programFeasible N (decode N u) :=
      ⟨encodeTrade N (zeroSigned N),by rw [decode_encode]; exact secondBestTradeZeroFeasible N⟩
    have hb : BddAbove {r | ∃ u, programFeasible N (decode N u) ∧ r = gainRow N u} := by
      refine ⟨FB N,?_⟩
      rintro r ⟨u,hu,rfl⟩
      rw [gainRow_apply]
      exact secondBestTradeGainsBound N _ hu
    obtain ⟨u,hu,he⟩ := TradePolyhedra.attain presentation (gainRow N) ne hb
    refine ⟨decode N u,hu,?_⟩
    rw [← gainRow_apply,he]
    unfold OPT
    congr 1
    ext r
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨decode N y,hy,gainRow_apply N y⟩
    · rintro ⟨m,hm,rfl⟩
      refine ⟨encodeTrade N m,by rwa [decode_encode],?_⟩
      rw [gainRow_apply,decode_encode]
