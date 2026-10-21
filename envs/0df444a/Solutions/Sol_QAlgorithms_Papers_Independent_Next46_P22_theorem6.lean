-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P22.theorem6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T15:49:14.808373+00:00
-- url     : https://prove2.me/submissions/8c6bb428-a546-4b18-9724-f5fc8dae3235

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

open Classical in
theorem solution {F H L : Type*} [Field F] [Ring H] [HopfAlgebra F H] [LieRing L] [LieAlgebra F L]
    [CharZero F] [FiniteDimensional F L]
    (hL : Semisimple F L) (alpha : H →ₐ[F] Module.End F L) (ha : ModuleLie alpha) :
    SimpleIdealDecomposition (ActionStable alpha) := by
  have l6 : ∀ M : Submodule F L, ActionStable alpha M → ActionStable alpha (Centralizer M) := by
    intro M hM h a haC b hb
    rw [G61P.key alpha ha h a b]
    unfold tensorSum
    refine Finset.sum_eq_zero (fun p _ => ?_)
    show alpha p.1 ⁅a, _⁆ = 0
    rw [haC _ (hM _ _ hb), map_zero]
  have hcompl : ∀ U W : Submodule F L, LieStable (L := L) U → ActionStable alpha U → W ≤ U →
      LieStable (L := L) W → ActionStable alpha W → ∃ W' : Submodule F L, W' ≤ U ∧
        LieStable (L := L) W' ∧ ActionStable alpha W' ∧ Disjoint W W' ∧ W ⊔ W' = U := by
    intro U W hU hUs hWU hW hWs
    refine ⟨U ⊓ Centralizer W, inf_le_left, fun a b hb => ⟨hU a b hb.1, G61K.centr_ideal W hW a b hb.2⟩,
      fun h b hb => ⟨hUs h b hb.1, l6 W hWs h b hb.2⟩,
      (G61K.disj hL W hW).mono_right inf_le_right, ?_⟩
    rw [inf_comm, ← sup_inf_assoc_of_le _ hWU, G61K.sup_top hL W hW, top_inf_eq]
  obtain ⟨S, hSi, hSs, hSirr⟩ := G61D.decomp_exists (L := L) (V := L) (ActionStable alpha) hcompl _ ⊤ rfl
    (fun a v _ => Submodule.mem_top) (fun h v _ => Submodule.mem_top)
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
