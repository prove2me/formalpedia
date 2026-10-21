-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P22.theorem7
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T15:50:44.072802+00:00
-- url     : https://prove2.me/submissions/cc744a2d-72dd-4c9c-bb23-ab374b5ff8b0

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P22

open QAlgorithms.Papers.Independent.Next46.P22
open scoped TensorProduct

namespace G61P

variable {F A B X : Type*} [Field F]
  [AddCommGroup A] [Module F A] [AddCommGroup B] [Module F B] [AddCommGroup X] [Module F X]

theorem ts_lift (z : A ⊗[F] B) (Φ : A →ₗ[F] B →ₗ[F] X) :
    tensorSum z (fun a b => Φ a b) = TensorProduct.lift Φ z := by
  unfold tensorSum
  conv_rhs => rw [(TensorProduct.exists_finset z).choose_spec]
  simp [map_sum]

theorem ts_eq (z : A ⊗[F] B) (f : A → B → X) (Φ : A →ₗ[F] B →ₗ[F] X)
    (h : ∀ a b, f a b = Φ a b) : tensorSum z f = TensorProduct.lift Φ z := by
  have : f = fun a b => Φ a b := funext fun a => funext fun b => h a b
  subst this; exact ts_lift z Φ

theorem ts_mem (z : A ⊗[F] B) (f : A → B → X) (U : Submodule F X) (h : ∀ a b, f a b ∈ U) :
    tensorSum z f ∈ U := by
  unfold tensorSum; exact Submodule.sum_mem _ (fun p _ => h _ _)

theorem ts_bil {C D : Type*} [AddCommGroup C] [Module F C] [AddCommGroup D] [Module F D]
    (z : A ⊗[F] B) (G : A →ₗ[F] B →ₗ[F] X) (f : A → B → X) (hf : ∀ a b, f a b = G a b)
    (z' : C ⊗[F] D) (u : C → D → A) (w : C → D → B)
    (hz : z = tensorSum z' (fun x y => u x y ⊗ₜ[F] w x y)) :
    tensorSum z f = tensorSum z' (fun x y => G (u x y) (w x y)) := by
  rw [ts_eq z f G hf, hz]
  unfold tensorSum
  rw [map_sum]
  simp

theorem map_ts {Y : Type*} [AddCommGroup Y] [Module F Y] (T : X →ₗ[F] Y) (z : A ⊗[F] B) (f : A → B → X) :
    T (tensorSum z f) = tensorSum z (fun a b => T (f a b)) := by
  unfold tensorSum; rw [map_sum]

variable {H L : Type*} [Ring H] [HopfAlgebra F H] [LieRing L] [LieAlgebra F L]

/-- bilinear map (x, w) ↦ ⁅α x u, α w v⁆ -/
def lam (alpha : H →ₐ[F] Module.End F L) (u v : L) : H →ₗ[F] H →ₗ[F] L :=
  LinearMap.mk₂ F (fun x w => ⁅alpha x u, alpha w v⁆)
    (by intro a b c; simp [add_lie]) (by intro c a b; simp [smul_lie])
    (by intro a b c; simp [lie_add]) (by intro c a b; simp [lie_smul])

theorem key (alpha : H →ₐ[F] Module.End F L) (ha : ModuleLie alpha) (h : H) (u v : L) :
    ⁅alpha h u, v⁆ = tensorSum (Coalgebra.comul (R := F) h)
      (fun h1 h2 => alpha h1 ⁅u, alpha (HopfAlgebra.antipode F h2) v⁆) := by
  -- Φ h1 h2 = α h1 ⁅u, α (S h2) v⁆
  let Φ : H →ₗ[F] H →ₗ[F] L := LinearMap.mk₂ F
    (fun h1 h2 => alpha h1 ⁅u, alpha (HopfAlgebra.antipode F h2) v⁆)
    (by intro a b c; simp) (by intro c a b; simp)
    (by intro a b c; simp) (by intro c a b; simp)
  rw [ts_eq _ (fun h1 h2 => alpha h1 ⁅u, alpha (HopfAlgebra.antipode F h2) v⁆) Φ (fun _ _ => rfl)]
  -- Θ' : H ⊗ (H ⊗ H) → L
  let Θ' : H ⊗[F] (H ⊗[F] H) →ₗ[F] L :=
    TensorProduct.lift (lam alpha u v) ∘ₗ
      (LinearMap.lTensor H (LinearMap.mul' F H ∘ₗ (HopfAlgebra.antipode F (A := H)).lTensor H))
  have hΦ : TensorProduct.lift Φ = Θ' ∘ₗ (TensorProduct.assoc F H H H).toLinearMap ∘ₗ
      (Coalgebra.comul (R := F) (A := H)).rTensor H := by
    apply TensorProduct.ext'
    intro h1 h2
    simp only [TensorProduct.lift.tmul, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.rTensor_tmul, LinearEquiv.coe_coe]
    show alpha h1 ⁅u, alpha (HopfAlgebra.antipode F h2) v⁆ = _
    rw [ha h1 u _]
    rw [ts_eq _ (fun x y => ⁅alpha x u, alpha y (alpha (HopfAlgebra.antipode F h2) v)⁆) (lam alpha u (alpha (HopfAlgebra.antipode F h2) v)) (fun _ _ => rfl)]
    induction (Coalgebra.comul (R := F) h1) using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      simp [Θ', lam, TensorProduct.assoc_tmul, Module.End.mul_apply]
    | add p q hp hq => rw [map_add, hp, hq, TensorProduct.add_tmul, map_add, map_add]
  rw [hΦ]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  rw [Coalgebra.coassoc_apply]
  have hΘ : Θ' ∘ₗ (Coalgebra.comul (R := F) (A := H)).lTensor H =
      TensorProduct.lift (lam alpha u v) ∘ₗ
        LinearMap.lTensor H ((Algebra.linearMap F H) ∘ₗ Coalgebra.counit) := by
    rw [← HopfAlgebra.mul_antipode_lTensor_comul]
    simp only [Θ', LinearMap.comp_assoc, ← LinearMap.lTensor_comp]
  have := congrArg (fun f => f (Coalgebra.comul (R := F) h)) hΘ
  simp only [LinearMap.coe_comp, Function.comp_apply] at this
  rw [this]
  rw [LinearMap.lTensor_comp, LinearMap.comp_apply, Coalgebra.lTensor_counit_comul]
  simp [lam]

theorem ts_lam (alpha : H →ₐ[F] Module.End F L) (u v : L) (z : H ⊗[F] H) :
    tensorSum z (fun h1 h2 => ⁅alpha h1 u, alpha h2 v⁆) = TensorProduct.lift (lam alpha u v) z :=
  ts_eq z (fun h1 h2 => ⁅alpha h1 u, alpha h2 v⁆) (lam alpha u v) (fun _ _ => rfl)

end G61P

open QAlgorithms.Papers.Independent.Next46.P22
open Classical

namespace G61Q

variable {F H V X : Type*} [Field F] [Ring H] [HopfAlgebra F H]
  [AddCommGroup V] [Module F V] [AddCommGroup X] [Module F X]

/-- comodule antipode collapse: Σ Λ(y0, y1 S(k)) = Λ(b, 1). -/
theorem coll (ρ : RightComodule F H V) (Λ : V →ₗ[F] H →ₗ[F] X) (b : V) :
    tensorSum (ρ.rho b) (fun y k => tensorSum (ρ.rho y)
      (fun y0 y1 => Λ y0 (y1 * HopfAlgebra.antipode F k))) = Λ b 1 := by
  let Θ' : V ⊗[F] (H ⊗[F] H) →ₗ[F] X := TensorProduct.lift Λ ∘ₗ
      LinearMap.lTensor V (LinearMap.mul' F H ∘ₗ (HopfAlgebra.antipode F (A := H)).lTensor H)
  let Θ : (V ⊗[F] H) ⊗[F] H →ₗ[F] X := Θ' ∘ₗ (TensorProduct.assoc F V H H).toLinearMap
  have hin : ∀ y k, tensorSum (ρ.rho y) (fun y0 y1 => Λ y0 (y1 * HopfAlgebra.antipode F k)) =
      Θ (ρ.rho y ⊗ₜ[F] k) := by
    intro y k
    let Λk : V →ₗ[F] H →ₗ[F] X := LinearMap.mk₂ F (fun y0 y1 => Λ y0 (y1 * HopfAlgebra.antipode F k))
      (by intro a b c; simp) (by intro c a b; simp)
      (by intro a b c; simp [add_mul]) (by intro c a b; simp)
    rw [G61P.ts_eq _ (fun y0 y1 => Λ y0 (y1 * HopfAlgebra.antipode F k)) Λk (fun _ _ => rfl)]
    induction (ρ.rho y) using TensorProduct.induction_on with
    | zero => simp
    | tmul x z => simp [Θ, Θ', Λk]
    | add p q hp hq => rw [map_add, hp, hq, TensorProduct.add_tmul, map_add]
  simp only [hin]
  let Φ : V →ₗ[F] H →ₗ[F] X := ((TensorProduct.mk F (V ⊗[F] H) H).compl₁₂ ρ.rho LinearMap.id).compr₂ Θ
  rw [G61P.ts_eq _ (fun y k => Θ (ρ.rho y ⊗ₜ[F] k))
    Φ (fun _ _ => rfl)]
  have h1 : TensorProduct.lift Φ (ρ.rho b) = Θ (TensorProduct.map ρ.rho LinearMap.id (ρ.rho b)) := by
    induction (ρ.rho b) using TensorProduct.induction_on with
    | zero => simp
    | tmul x z => simp; rfl
    | add p q hp hq => rw [map_add, hp, hq, map_add, map_add]
  rw [h1]
  simp only [Θ, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  rw [ρ.coassoc b]
  have h2 : Θ' (TensorProduct.map LinearMap.id (Coalgebra.comul (R := F)) (ρ.rho b)) =
      TensorProduct.lift Λ (LinearMap.lTensor V ((Algebra.linearMap F H) ∘ₗ Coalgebra.counit) (ρ.rho b)) := by
    rw [← HopfAlgebra.mul_antipode_lTensor_comul]
    simp only [Θ', LinearMap.coe_comp, Function.comp_apply]
    rw [← LinearMap.lTensor_def, ← LinearMap.comp_apply (LinearMap.lTensor V _) (LinearMap.lTensor V _),
      ← LinearMap.lTensor_comp]
    simp only [LinearMap.comp_assoc]
  rw [h2]
  conv_rhs => rw [← ρ.counital b]
  induction (ρ.rho b) using TensorProduct.induction_on with
  | zero => simp
  | tmul x z =>
    simp
    rw [Algebra.algebraMap_eq_smul_one, map_smul]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add, map_add, LinearMap.add_apply]

end G61Q

theorem G61Q.l7 {F H L : Type*} [Field F] [Ring H] [HopfAlgebra F H] [LieRing L] [LieAlgebra F L]
    (rho : RightComodule F H L) (hr : ComoduleLie rho)
    (M : Submodule F L) (hM : CoStable rho M) :
    CoStable rho (Centralizer M) := by
  intro a ha
  -- Step A
  have hA : ∀ b ∈ M, tensorSum (rho.rho a) (fun a0 a1 => ⁅a0, b⁆ ⊗ₜ[F] a1) = 0 := by
    intro b hb
    let Λ : L → H → L →ₗ[F] H →ₗ[F] L ⊗[F] H := fun a0 a1 => LinearMap.mk₂ F
      (fun y0 w => ⁅a0, y0⁆ ⊗ₜ[F] (a1 * w))
      (by intro x y z; simp [lie_add, TensorProduct.add_tmul]) (by intro c x y; simp [lie_smul, TensorProduct.smul_tmul'])
      (by intro x y z; simp [mul_add, TensorProduct.tmul_add]) (by intro c x y; simp [TensorProduct.tmul_smul])
    have e1 : ∀ (a0 : L) (a1 : H), ⁅a0, b⁆ ⊗ₜ[F] a1 = tensorSum (rho.rho b) (fun y k => tensorSum (rho.rho y)
        (fun y0 y1 => ⁅a0, y0⁆ ⊗ₜ[F] (a1 * (y1 * HopfAlgebra.antipode F k)))) := by
      intro a0 a1
      have h := G61Q.coll rho (Λ a0 a1) b
      rw [show ((Λ a0 a1) b) 1 = ⁅a0, b⁆ ⊗ₜ[F] a1 from (show ⁅a0, b⁆ ⊗ₜ[F] (a1 * 1) = ⁅a0, b⁆ ⊗ₜ[F] a1 by rw [mul_one])] at h
      exact h.symm
    simp only [e1]
    let R : H → L ⊗[F] H →ₗ[F] L ⊗[F] H := fun k =>
      LinearMap.lTensor L ((LinearMap.mul F H).flip (HopfAlgebra.antipode F k))
    have e2 : ∀ (y : L) (k : H), tensorSum (rho.rho a) (fun a0 a1 => tensorSum (rho.rho y)
        (fun y0 y1 => ⁅a0, y0⁆ ⊗ₜ[F] (a1 * (y1 * HopfAlgebra.antipode F k)))) = R k (rho.rho ⁅a, y⁆) := by
      intro y k
      rw [hr a y, G61P.map_ts]
      unfold tensorSum
      refine Finset.sum_congr rfl (fun p _ => ?_)
      dsimp only
      rw [map_sum]
      refine Finset.sum_congr rfl (fun q _ => ?_)
      simp [R, mul_assoc]
    unfold tensorSum
    rw [Finset.sum_comm]
    have e3 := fun (q : L × H) => e2 q.1 q.2
    unfold tensorSum at e3
    simp only [e3]
    let Ψ : L →ₗ[F] H →ₗ[F] L ⊗[F] H := LinearMap.mk₂ F (fun y k => R k (rho.rho ⁅a, y⁆))
      (by intro x y z; simp [lie_add]) (by intro c x y; simp [lie_smul])
      (by intro x y z; simp [R, LinearMap.lTensor_add]) (by intro c x y; simp [R, LinearMap.lTensor_smul])
    have e4 := G61P.ts_lift (rho.rho b) Ψ
    unfold tensorSum at e4
    simp only [Ψ, LinearMap.mk₂_apply] at e4
    rw [e4]
    have hb' := hM b hb
    unfold coactionTensorImage at hb'
    generalize rho.rho b = z at hb' ⊢
    induction hb' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨v, hv, h, rfl⟩ := hx
      simp [Ψ, ha v hv]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul c x _ hx => rw [map_smul, hx, smul_zero]
  -- Step B
  let e := Module.Free.chooseBasis F H
  let E := TensorProduct.equivFinsuppOfBasisRight (M := L) e
  set c := E (rho.rho a) with hc
  have hρ : rho.rho a = c.sum (fun i m => m ⊗ₜ[F] e i) := by
    rw [← TensorProduct.equivFinsuppOfBasisRight_symm_apply, hc, LinearEquiv.symm_apply_apply]
  have hci : ∀ i, c i ∈ Centralizer M := by
    intro i b hb
    have h0 := hA b hb
    let Φb : L →ₗ[F] H →ₗ[F] L ⊗[F] H := LinearMap.mk₂ F (fun x h => ⁅x, b⁆ ⊗ₜ[F] h)
      (by intro x y z; simp [add_lie, TensorProduct.add_tmul]) (by intro c x y; simp [smul_lie, TensorProduct.smul_tmul'])
      (by intro x y z; simp [TensorProduct.tmul_add]) (by intro c x y; simp [TensorProduct.tmul_smul])
    rw [G61P.ts_eq _ (fun a0 a1 => ⁅a0, b⁆ ⊗ₜ[F] a1) Φb (fun _ _ => rfl), hρ] at h0
    have h1 : E.symm (c.mapRange (fun x => ⁅x, b⁆) (by simp)) = 0 := by
      rw [TensorProduct.equivFinsuppOfBasisRight_symm_apply, Finsupp.sum_mapRange_index (by simp)]
      rw [← h0, Finsupp.sum, Finsupp.sum, map_sum]
      exact Finset.sum_congr rfl (fun _ _ => rfl)
    have h2 := congrArg (fun f => f i) (E.symm.injective (h1.trans (map_zero E.symm).symm))
    simpa using h2
  rw [hρ]
  unfold coactionTensorImage
  exact Submodule.sum_mem _ (fun i _ => Submodule.subset_span ⟨c i, hci i, e i, rfl⟩)

open Classical

namespace G61D

theorem insert_indep {α : Type*} [CompleteLattice α] [IsModularLattice α]
    (S' : Set α) (W : α) (h : sSupIndep S') (hd : Disjoint W (sSup S')) (hW : W ∉ S') :
    sSupIndep (insert W S') := by
  intro a ha
  rcases ha with rfl | ha
  · rw [Set.insert_sdiff_of_mem _ (Set.mem_singleton _), Set.sdiff_singleton_eq_self hW]; exact hd
  · have haW : a ≠ W := fun e => hW (e ▸ ha)
    rw [Set.insert_sdiff_of_notMem _ (by simpa using haW.symm), sSup_insert]
    have h1 : Disjoint a (sSup (S' \ {a})) := h ha
    have h2 : Disjoint (a ⊔ sSup (S' \ {a})) W := by
      refine Disjoint.symm (hd.mono_right (sup_le (le_sSup ha) (sSup_le_sSup Set.sdiff_subset)))
    rw [sup_comm]
    exact h1.disjoint_sup_right_of_disjoint_sup_left h2

theorem decomp_exists {F V L : Type*} [Field F] [AddCommGroup V] [Module F V] [LieRing L] [LieAlgebra F L]
    [LieRingModule L V] [LieModule F L V] [FiniteDimensional F V] (stable : Submodule F V → Prop)
    (hcompl : ∀ U W : Submodule F V, LieStable (L := L) U → stable U → W ≤ U → LieStable (L := L) W →
      stable W → ∃ W' : Submodule F V, W' ≤ U ∧ LieStable (L := L) W' ∧ stable W' ∧
        Disjoint W W' ∧ W ⊔ W' = U) :
    ∀ n (U : Submodule F V), Module.finrank F U = n → LieStable (L := L) U → stable U →
      ∃ S : Finset (Submodule F V), sSupIndep (S : Set (Submodule F V)) ∧ sSup (S : Set (Submodule F V)) = U ∧
        ∀ P ∈ S, IrreducibleIn (L := L) (stable) P := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro U hn hU hUg
  by_cases hU0 : U = ⊥
  · exact ⟨∅, by simp, by simp [hU0], by simp⟩
  -- minimal nonzero stable graded W ≤ U
  have hex : ∃ k, ∃ W : Submodule F V, W ≤ U ∧ W ≠ ⊥ ∧ LieStable (L := L) W ∧ stable W ∧
      Module.finrank F W = k := ⟨_, U, le_rfl, hU0, hU, hUg, rfl⟩
  obtain ⟨W, hWU, hW0, hW, hWg, hWk⟩ := Nat.find_spec hex
  have hmin : ∀ W2 : Submodule F V, W2 ≤ U → W2 ≠ ⊥ → LieStable (L := L) W2 → stable W2 →
      Nat.find hex ≤ Module.finrank F W2 := fun W2 a b c d => Nat.find_min' hex ⟨W2, a, b, c, d, rfl⟩
  have hirr : IrreducibleIn (L := L) (stable) W := by
    refine ⟨hW, hWg, fun W2 h2 hs hg => ?_⟩
    by_cases h20 : W2 = ⊥
    · exact Or.inl h20
    · right
      exact Submodule.eq_of_le_of_finrank_le h2 (hWk ▸ hmin W2 (h2.trans hWU) h20 hs hg)
  obtain ⟨W', hW'U, hW', hW'g, hdis, hsup⟩ := hcompl U W hU hUg hWU hW hWg
  have hdim : Module.finrank F W' < n := by
    have := Submodule.finrank_sup_add_finrank_inf_eq W W'
    rw [hsup, hdis.eq_bot, finrank_bot, add_zero] at this
    have hpos : 0 < Module.finrank F W :=
      Nat.pos_of_ne_zero (fun h => hW0 (Submodule.finrank_eq_zero.mp h))
    omega
  obtain ⟨S', hS'i, hS's, hS'irr⟩ := ih _ hdim W' rfl hW' hW'g
  have hWS' : W ∉ S' := by
    intro hm
    have : W ≤ W' := hS's ▸ le_sSup (Finset.mem_coe.mpr hm)
    exact hW0 (by rw [← inf_eq_left.mpr this, hdis.eq_bot])
  refine ⟨insert W S', ?_, ?_, ?_⟩
  · rw [Finset.coe_insert]
    exact insert_indep _ W hS'i (hS's ▸ hdis) (by simpa using hWS')
  · rw [Finset.coe_insert, sSup_insert, hS's, hsup]
  · intro P hP
    rcases Finset.mem_insert.mp hP with rfl | hP
    · exact hirr
    · exact hS'irr P hP


end G61D

namespace G61K

variable {F L : Type*} [Field F] [CharZero F] [LieRing L] [LieAlgebra F L] [FiniteDimensional F L]

def toIdeal (W : Submodule F L) (hW : ∀ (a : L), ∀ b ∈ W, ⁅a, b⁆ ∈ W) : LieIdeal F L :=
  { W with lie_mem := fun {x m} h => hW x m h }

omit [CharZero F] [FiniteDimensional F L] in
theorem centr_ideal (W : Submodule F L) (hW : ∀ (a : L), ∀ b ∈ W, ⁅a, b⁆ ∈ W) :
    ∀ (a : L), ∀ c ∈ Centralizer W, ⁅a, c⁆ ∈ Centralizer W := by
  intro a c hc w hw
  rw [lie_lie, hc w hw, hc _ (hW a w hw), lie_zero, sub_zero]

theorem disj (hL : LieAlgebra.radical F L = ⊥) (W : Submodule F L)
    (hW : ∀ (a : L), ∀ b ∈ W, ⁅a, b⁆ ∈ W) : Disjoint W (Centralizer W) := by
  haveI : LieAlgebra.HasTrivialRadical F L := ⟨hL⟩
  let J : LieIdeal F L := toIdeal (W ⊓ Centralizer W) (fun a b hb =>
    ⟨hW a b hb.1, centr_ideal W hW a b hb.2⟩)
  haveI : IsLieAbelian J := ⟨fun x y => by
    apply Subtype.ext
    show ⁅(x : L), (y : L)⁆ = 0
    have hy : (y : L) ∈ Centralizer W := y.2.2
    rw [← lie_skew, hy x x.2.1, neg_zero]⟩
  have hJ : J = ⊥ := LieAlgebra.IsKilling.ideal_eq_bot_of_isLieAbelian J
  rw [disjoint_iff]
  have : LieSubmodule.toSubmodule J = ⊥ := by rw [hJ]; rfl
  exact this

theorem sup_top (hL : LieAlgebra.radical F L = ⊥) (W : Submodule F L)
    (hW : ∀ (a : L), ∀ b ∈ W, ⁅a, b⁆ ∈ W) : W ⊔ Centralizer W = ⊤ := by
  haveI : LieAlgebra.HasTrivialRadical F L := ⟨hL⟩
  let I := toIdeal W hW
  have hc := LieIdeal.isCompl_killingCompl I
  have hK : LieSubmodule.toSubmodule (LieIdeal.killingCompl F L I) ≤ Centralizer W := by
    intro x hx w hw
    have h1 : ⁅x, w⁆ ∈ I := I.lie_mem hw
    have h2 : ⁅x, w⁆ ∈ LieIdeal.killingCompl F L I := by
      rw [← lie_skew]; exact Submodule.neg_mem _ ((LieIdeal.killingCompl F L I).lie_mem hx)
    have := hc.disjoint
    rw [disjoint_iff] at this
    have h3 : ⁅x, w⁆ ∈ I ⊓ LieIdeal.killingCompl F L I := ⟨h1, h2⟩
    rw [this] at h3
    simpa using h3
  have htop : LieSubmodule.toSubmodule I ⊔ LieSubmodule.toSubmodule (LieIdeal.killingCompl F L I) = ⊤ := by
    rw [← LieSubmodule.sup_toSubmodule, hc.sup_eq_top]; rfl
  rw [eq_top_iff, ← htop]
  exact sup_le_sup le_rfl hK

end G61K


namespace G61R

variable {F H V : Type*} [Field F] [Ring H] [HopfAlgebra F H] [AddCommGroup V] [Module F V]

theorem mem_img (A : Submodule F V) (z : V ⊗[F] H) :
    z ∈ (coactionTensorImage A : Submodule F (V ⊗[F] H)) ↔
      ∀ i, TensorProduct.equivFinsuppOfBasisRight (M := V) (Module.Free.chooseBasis F H) z i ∈ A := by
  let e := Module.Free.chooseBasis F H
  let E := TensorProduct.equivFinsuppOfBasisRight (M := V) e
  constructor
  · intro hz
    unfold coactionTensorImage at hz
    induction hz using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨v, hv, h, rfl⟩ := hy
      intro i
      rw [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
      exact A.smul_mem _ hv
    | zero => intro i; simp
    | add a b _ _ ha hb => intro i; rw [map_add, Finsupp.add_apply]; exact A.add_mem (ha i) (hb i)
    | smul c a _ ha => intro i; rw [map_smul, Finsupp.smul_apply]; exact A.smul_mem c (ha i)
  · intro h
    have : z = (E z).sum (fun i m => m ⊗ₜ[F] e i) := by
      rw [← TensorProduct.equivFinsuppOfBasisRight_symm_apply, LinearEquiv.symm_apply_apply]
    rw [this]
    unfold coactionTensorImage
    exact Submodule.sum_mem _ (fun i _ => Submodule.subset_span ⟨E z i, h i, e i, rfl⟩)

theorem costable_inf (rho : RightComodule F H V) (A B : Submodule F V)
    (hA : CoStable rho A) (hB : CoStable rho B) : CoStable rho (A ⊓ B) := by
  intro v hv
  rw [mem_img]
  intro i
  exact ⟨(mem_img A _).mp (hA v hv.1) i, (mem_img B _).mp (hB v hv.2) i⟩

theorem costable_top (rho : RightComodule F H V) : CoStable rho ⊤ := by
  intro v _
  rw [mem_img]; intro i; exact Submodule.mem_top

end G61R

open Classical in
theorem solution {F H L : Type*} [Field F] [Ring H] [HopfAlgebra F H] [LieRing L] [LieAlgebra F L]
    [CharZero F] [FiniteDimensional F L]
    (hL : Semisimple F L) (rho : RightComodule F H L) (hr : ComoduleLie rho) :
    SimpleIdealDecomposition (CoStable rho) := by
  have hcompl : ∀ U W : Submodule F L, LieStable (L := L) U → CoStable rho U → W ≤ U →
      LieStable (L := L) W → CoStable rho W → ∃ W' : Submodule F L, W' ≤ U ∧
        LieStable (L := L) W' ∧ CoStable rho W' ∧ Disjoint W W' ∧ W ⊔ W' = U := by
    intro U W hU hUs hWU hW hWs
    refine ⟨U ⊓ Centralizer W, inf_le_left, fun a b hb => ⟨hU a b hb.1, G61K.centr_ideal W hW a b hb.2⟩,
      G61R.costable_inf rho _ _ hUs (G61Q.l7 rho hr W hWs),
      (G61K.disj hL W hW).mono_right inf_le_right, ?_⟩
    rw [inf_comm, ← sup_inf_assoc_of_le _ hWU, G61K.sup_top hL W hW, top_inf_eq]
  obtain ⟨S, hSi, hSs, hSirr⟩ := G61D.decomp_exists (L := L) (V := L) (CoStable rho) hcompl _ ⊤ rfl
    (fun a v _ => Submodule.mem_top) (G61R.costable_top rho)
  let e := S.equivFin
  refine ⟨S.card, fun i => G61K.toIdeal (e.symm i).1 (hSirr _ (e.symm i).2).1, ?_, ?_, fun i => ⟨?_, ?_⟩⟩
  · exact ((sSupIndep_iff _).mp hSi).comp e.symm.injective
  · show (⨆ i, (e.symm i).1) = ⊤
    rw [← hSs, sSup_eq_iSup']
    exact (e.symm.iSup_comp (g := fun x : (S : Set (Submodule F L)) => x.1))
  · exact (hSirr _ (e.symm i).2).2.1
  · intro U hUP hUid hUs
    set P := (e.symm i).1 with hPdef
    have hirr := hSirr _ (e.symm i).2
    have hPid : ∀ (a : L), ∀ b ∈ P, ⁅a, b⁆ ∈ P := hirr.1
    have hUL : LieStable (L := L) U := by
      intro a b hb
      have ha' : a ∈ P ⊔ Centralizer P := by rw [G61K.sup_top hL P hPid]; exact Submodule.mem_top
      obtain ⟨p, hp, c, hc, rfl⟩ := Submodule.mem_sup.mp ha'
      rw [add_lie, (show ⁅c, b⁆ = 0 from hc b (hUP hb)), add_zero]
      exact hUid p hp b hb
    exact hirr.2.2 U hUP hUL hUs
