-- Prove2me | solution 1 for XorParallelRepetition.Exponential.blr_no_commuting_embedding
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:28:44.748111+00:00
-- url     : https://prove2.me/submissions/e33f5847-0507-4ecb-ac76-443a5cfe8ccc

import Mathlib
import Definitions.Def_XorParallelRepetition_Exponential_XorGames
import Definitions.Def_XorParallelRepetition_Exponential_BLR
import Definitions.Def_XorParallelRepetition_Exponential_Embedding
universe u

section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace XorParallelRepetition.Dev.BlrNoEmb

open XorParallelRepetition.Exponential Finset

/-! ### Phases -/

section Phase

variable {p : ℕ} [Fact p.Prime]

theorem omega_prim : IsPrimitiveRoot (omega p) p :=
  Complex.isPrimitiveRoot_exp p (Fact.out : p.Prime).ne_zero

theorem phase_zero : phase p 0 = 1 := by
  simp [phase]

theorem phase_add (a b : ZMod p) : phase p (a + b) = phase p a * phase p b := by
  unfold phase
  rw [← pow_add, ZMod.val_add]
  conv_rhs => rw [← Nat.mod_add_div (a.val + b.val) p, pow_add, pow_mul,
    (omega_prim (p := p)).pow_eq_one, one_pow, mul_one]

theorem phase_eq_one {a : ZMod p} (h : phase p a = 1) : a = 0 := by
  unfold phase at h
  rw [omega_prim.pow_eq_one_iff_dvd] at h
  rw [← ZMod.val_eq_zero]
  exact Nat.eq_zero_of_dvd_of_lt h (ZMod.val_lt a)

end Phase

/-! ### Generic noncommutative products -/

theorem pw {M : Type*} [Monoid M] {κ : Type*} {f : κ → M} (h : ∀ i j, i ≠ j → Commute (f i) (f j))
    (s : Finset κ) : (s : Set κ).Pairwise (Function.onFun Commute f) :=
  fun i _ j _ hij => h i j hij

section Group

variable {G : Type*} [Group G] {κ : Type*}

theorem comm_mul_inv (f g : κ → G)
    (hff : ∀ i j, i ≠ j → Commute (f i) (f j)) (hgg : ∀ i j, i ≠ j → Commute (g i) (g j))
    (hfg : ∀ i j, i ≠ j → Commute (f i) (g j)) (i j : κ) (h : i ≠ j) :
    Commute (f i * (g i)⁻¹) (f j * (g j)⁻¹) :=
  Commute.mul_left ((hff i j h).mul_right (hfg i j h).inv_right)
    (((hfg j i (Ne.symm h)).symm.inv_left).mul_right ((hgg i j h).inv_left.inv_right))

theorem ncp_mul_inv [DecidableEq κ] (s : Finset κ) (f g : κ → G)
    (hff : ∀ i j, i ≠ j → Commute (f i) (f j)) (hgg : ∀ i j, i ≠ j → Commute (g i) (g j))
    (hfg : ∀ i j, i ≠ j → Commute (f i) (g j)) :
    s.noncommProd f (pw hff s) * (s.noncommProd g (pw hgg s))⁻¹
      = s.noncommProd (fun i => f i * (g i)⁻¹) (pw (comm_mul_inv f g hff hgg hfg) s) := by
  induction s using Finset.induction_on with
  | empty => simp only [noncommProd_empty, inv_one, mul_one]
  | insert a s ha ih =>
    rw [noncommProd_insert_of_notMem _ _ _ _ ha, noncommProd_insert_of_notMem _ _ _ _ ha,
      noncommProd_insert_of_notMem _ _ _ _ ha, ← ih]
    have hc : Commute (s.noncommProd f (pw hff s) * (s.noncommProd g (pw hgg s))⁻¹) (g a)⁻¹ := by
      apply Commute.inv_right
      apply Commute.mul_left
      · exact (noncommProd_commute _ _ _ _ fun i hi => (hfg i a (by rintro rfl; exact ha hi)).symm).symm
      · apply Commute.inv_left
        exact (noncommProd_commute _ _ _ _ fun i hi => (hgg i a (by rintro rfl; exact ha hi)).symm).symm
    rw [mul_inv_rev, mul_assoc (f a), mul_assoc (f a), ← mul_assoc _ _ (g a)⁻¹, hc.eq]

end Group

/-! ### The abstract setting -/

/-- The commuting product `∏ᵢ f i (x i) (β i)`. -/
noncomputable def mprod {ι : Type} [Fintype ι] {Q : ι → Type*} {p : ℕ} {G : Type*} [Monoid G]
    (f : ∀ i, Q i → ZMod p → G)
    (hf : ∀ i j, i ≠ j → ∀ y y' c c', Commute (f i y c) (f j y' c'))
    (x : ∀ i, Q i) (β : ι → ZMod p) : G :=
  Finset.univ.noncommProd (fun i => f i (x i) (β i)) (fun i _ j _ h => hf i j h _ _ _ _)

/-- The data extracted from a commuting embedding of the BLR game: operators `a` of the players
`i` and `b` of the players `i'`, acting on `V` through `ρ`. -/
structure Setup (ι : Type) [Fintype ι] (Q : ι → Type*) (p : ℕ) (G : Type*) [Group G]
    (V : Type*) [AddCommGroup V] [Module ℂ V] where
  ρ : G →* Module.End ℂ V
  a : ∀ i, Q i → ZMod p → G
  b : ∀ i, Q i → ZMod p → G
  hab : ∀ i j (y : Q i) (y' : Q j) (c c' : ZMod p), Commute (a i y c) (b j y' c')
  haa : ∀ i j, i ≠ j → ∀ (y : Q i) (y' : Q j) (c c' : ZMod p), Commute (a i y c) (a j y' c')
  hbb : ∀ i j, i ≠ j → ∀ (y : Q i) (y' : Q j) (c c' : ZMod p), Commute (b i y c) (b j y' c')
  S : Set (∀ i, Q i)
  t : (∀ i, Q i) → ZMod p
  v : V
  hv : v ≠ 0
  heig : ∀ x ∈ S, ∀ (α : ι → ZMod p) (γ : ZMod p),
    ρ (mprod b hbb x (fun i => α i + γ) * mprod a haa x α) v = phase p (γ * t x) • v

namespace Setup

variable {ι : Type} [Fintype ι] [DecidableEq ι] {Q : ι → Type*} {p : ℕ} [Fact p.Prime]
  {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
  (P : Setup ι Q p G V)

noncomputable def Mb (x : ∀ i, Q i) (β : ι → ZMod p) : G := mprod P.b P.hbb x β
noncomputable def Ma (x : ∀ i, Q i) (β : ι → ZMod p) : G := mprod P.a P.haa x β

def Bgrp : Subgroup G :=
  Subgroup.closure (Set.range fun z : (Σ i, Q i) × ZMod p => P.b z.1.1 z.1.2 z.2)

def Agrp : Subgroup G :=
  Subgroup.closure (Set.range fun z : (Σ i, Q i) × ZMod p => P.a z.1.1 z.1.2 z.2)

def Cent : Subalgebra ℂ (Module.End ℂ V) :=
  Subalgebra.centralizer ℂ (P.ρ '' (P.Bgrp : Set G))

def W : Submodule ℂ V :=
  (Subalgebra.toSubmodule P.Cent).map (LinearMap.applyₗ (R := ℂ) (M₂ := V) P.v)

theorem b_mem (i : ι) (y : Q i) (c : ZMod p) : P.b i y c ∈ P.Bgrp :=
  Subgroup.subset_closure ⟨(⟨i, y⟩, c), rfl⟩

theorem a_mem (i : ι) (y : Q i) (c : ZMod p) : P.a i y c ∈ P.Agrp :=
  Subgroup.subset_closure ⟨(⟨i, y⟩, c), rfl⟩

theorem Mb_mem (x : ∀ i, Q i) (β : ι → ZMod p) : P.Mb x β ∈ P.Bgrp := by
  unfold Mb mprod
  exact Subgroup.noncommProd_mem _ _ fun i _ => P.b_mem _ _ _

theorem Ma_mem (x : ∀ i, Q i) (β : ι → ZMod p) : P.Ma x β ∈ P.Agrp := by
  unfold Ma mprod
  exact Subgroup.noncommProd_mem _ _ fun i _ => P.a_mem _ _ _

theorem A_comm_B {g h : G} (hg : g ∈ P.Agrp) (hh : h ∈ P.Bgrp) : Commute g h := by
  have h1 : P.Agrp ≤ Subgroup.centralizer (P.Bgrp : Set G) := by
    rw [Agrp, Subgroup.closure_le]
    rintro _ ⟨z, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro h' hh'
    have h2 : P.Bgrp ≤ Subgroup.centralizer {P.a z.1.1 z.1.2 z.2} := by
      rw [Bgrp, Subgroup.closure_le]
      rintro _ ⟨z', rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact (P.hab _ _ _ _ _ _).eq.symm
    exact (Subgroup.mem_centralizer_singleton_iff.mp (h2 hh'))
  exact ((Subgroup.mem_centralizer_iff.mp (h1 hg)) h hh).symm

theorem rhoA_mem {g : G} (hg : g ∈ P.Agrp) : P.ρ g ∈ P.Cent := by
  rw [Cent, Subalgebra.mem_centralizer_iff]
  rintro _ ⟨h, hh, rfl⟩
  rw [← map_mul, ← map_mul, (P.A_comm_B hg hh).eq]

theorem rhoB_comm {h : G} (hh : h ∈ P.Bgrp) {Y : Module.End ℂ V} (hY : Y ∈ P.Cent) :
    P.ρ h * Y = Y * P.ρ h := by
  rw [Cent, Subalgebra.mem_centralizer_iff] at hY
  exact hY _ ⟨h, hh, rfl⟩

theorem mem_W {w : V} : w ∈ P.W ↔ ∃ Y ∈ P.Cent, Y P.v = w := by
  simp [W]

theorem v_mem : P.v ∈ P.W := P.mem_W.mpr ⟨1, P.Cent.one_mem, rfl⟩

theorem W_A {g : G} (hg : g ∈ P.Agrp) {w : V} (hw : w ∈ P.W) : P.ρ g w ∈ P.W := by
  obtain ⟨Y, hY, rfl⟩ := P.mem_W.mp hw
  exact P.mem_W.mpr ⟨P.ρ g * Y, P.Cent.mul_mem (P.rhoA_mem hg) hY, rfl⟩

theorem W_B_of_v {h : G} (hh : h ∈ P.Bgrp) (hv : P.ρ h P.v ∈ P.W) {w : V} (hw : w ∈ P.W) :
    P.ρ h w ∈ P.W := by
  obtain ⟨Y, hY, rfl⟩ := P.mem_W.mp hw
  obtain ⟨Z, hZ, hZv⟩ := P.mem_W.mp hv
  refine P.mem_W.mpr ⟨Y * Z, P.Cent.mul_mem hY hZ, ?_⟩
  symm
  calc P.ρ h (Y P.v) = (P.ρ h * Y) P.v := rfl
    _ = (Y * P.ρ h) P.v := by rw [P.rhoB_comm hh hY]
    _ = Y (Z P.v) := by rw [Module.End.mul_apply, hZv]
    _ = (Y * Z) P.v := rfl

theorem W_B_scalar {h : G} (hh : h ∈ P.Bgrp) {c : ℂ} (hv : P.ρ h P.v = c • P.v) {w : V}
    (hw : w ∈ P.W) : P.ρ h w = c • w := by
  obtain ⟨Y, hY, rfl⟩ := P.mem_W.mp hw
  rw [← Module.End.mul_apply, P.rhoB_comm hh hY, Module.End.mul_apply, hv, map_smul]

theorem rho_inv_apply (g : G) (u : V) : P.ρ g⁻¹ (P.ρ g u) = u := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem rho_inj (g : G) {u w : V} (h : P.ρ g u = P.ρ g w) : u = w := by
  rw [← P.rho_inv_apply g u, h, P.rho_inv_apply]

theorem rho_mul_apply (g h : G) (u : V) : P.ρ (g * h) u = P.ρ g (P.ρ h u) := by
  rw [map_mul, Module.End.mul_apply]

/-- `γ = 0` in the eigenvalue equation. -/
theorem vA {x : ∀ i, Q i} (hx : x ∈ P.S) (β : ι → ZMod p) :
    P.ρ (P.Mb x β)⁻¹ P.v = P.ρ (P.Ma x β) P.v ∧ P.ρ (P.Mb x β) P.v = P.ρ (P.Ma x β)⁻¹ P.v := by
  have h := P.heig x hx β 0
  simp only [add_zero, zero_mul, phase_zero, one_smul] at h
  change P.ρ (P.Mb x β * P.Ma x β) P.v = P.v at h
  constructor
  · conv_lhs => rw [← h]
    rw [← P.rho_mul_apply, ← mul_assoc, inv_mul_cancel, one_mul]
  · have hc := (P.A_comm_B (P.Ma_mem x β) (P.Mb_mem x β)).eq
    rw [← hc] at h
    conv_rhs => rw [← h]
    rw [← P.rho_mul_apply, ← mul_assoc, inv_mul_cancel, one_mul]

theorem R1 {x : ∀ i, Q i} (hx : x ∈ P.S) (α : ι → ZMod p) (γ : ZMod p) {w : V} (hw : w ∈ P.W) :
    P.ρ (P.Mb x (fun i => α i + γ) * (P.Mb x α)⁻¹) w = phase p (γ * P.t x) • w := by
  refine P.W_B_scalar (P.Bgrp.mul_mem (P.Mb_mem _ _) (P.Bgrp.inv_mem (P.Mb_mem _ _))) ?_ hw
  rw [P.rho_mul_apply, (P.vA hx α).1, ← P.rho_mul_apply]
  exact P.heig x hx α γ

/-! ### Splitting off one player -/

noncomputable def R (x : ∀ i, Q i) (i : ι) (β : ι → ZMod p) : G :=
  (univ.erase i).noncommProd (fun j => P.b j (x j) (β j))
    (fun j _ k _ h => P.hbb j k h _ _ _ _)

theorem Mb_eq (x : ∀ i, Q i) (i : ι) (β : ι → ZMod p) :
    P.Mb x β = P.b i (x i) (β i) * P.R x i β := by
  unfold Mb mprod R
  exact (mul_noncommProd_erase _ (mem_univ i) _ _).symm

theorem R_congr (x : ∀ i, Q i) (i : ι) {β β' : ι → ZMod p} (h : ∀ j, j ≠ i → β j = β' j) :
    P.R x i β = P.R x i β' :=
  noncommProd_congr rfl (fun j hj => by rw [h j (ne_of_mem_erase hj)]) _

theorem R_comm (x : ∀ i, Q i) (i : ι) (β : ι → ZMod p) (y : Q i) (c : ZMod p) :
    Commute (P.R x i β) (P.b i y c) :=
  (noncommProd_commute _ _ _ _ fun j hj => (P.hbb j i (ne_of_mem_erase hj) _ _ _ _).symm).symm

noncomputable def K (x : ∀ i, Q i) (i : ι) (c : ZMod p) : G :=
  P.R x i (fun _ => c) * (P.R x i 0)⁻¹

theorem K_comm (x : ∀ i, Q i) (i : ι) (c : ZMod p) (y : Q i) (d : ZMod p) :
    Commute (P.K x i c) (P.b i y d) :=
  (P.R_comm _ _ _ _ _).mul_left (P.R_comm _ _ _ _ _).inv_left

/-- The operators `E_i(y, c) = U_{i'}(y, c) U_{i'}(y, 0)^*`. -/
def E (i : ι) (y : Q i) (c : ZMod p) : G := P.b i y c * (P.b i y 0)⁻¹

theorem E_mem (i : ι) (y : Q i) (c : ZMod p) : P.E i y c ∈ P.Bgrp :=
  P.Bgrp.mul_mem (P.b_mem _ _ _) (P.Bgrp.inv_mem (P.b_mem _ _ _))

theorem E_zero (i : ι) (y : Q i) : P.E i y 0 = 1 := mul_inv_cancel _

theorem key_identity (x : ∀ i, Q i) (i : ι) (a c : ZMod p) :
    P.Mb x (fun j => Function.update (0 : ι → ZMod p) i a j + c) *
        (P.Mb x (Function.update (0 : ι → ZMod p) i a))⁻¹
      = P.K x i c * (P.b i (x i) (a + c) * (P.b i (x i) a)⁻¹) := by
  rw [P.Mb_eq x i, P.Mb_eq x i (Function.update 0 i a)]
  simp only [Function.update_self]
  rw [P.R_congr x i (β' := fun _ => c) (fun j hj => by simp [Function.update_of_ne hj]),
    P.R_congr x i (β := Function.update 0 i a) (β' := 0)
      (fun j hj => by simp [Function.update_of_ne hj])]
  have hK := (P.K_comm x i c (x i) (a + c)).eq
  unfold K at hK ⊢
  rw [mul_inv_rev, ← mul_assoc, mul_assoc (P.b i (x i) (a + c)), ← hK]
  group

theorem R2' {x : ∀ i, Q i} (hx : x ∈ P.S) (i : ι) (c : ZMod p) {w : V} (hw : w ∈ P.W) :
    P.ρ (P.K x i c * P.E i (x i) c) w = phase p (c * P.t x) • w := by
  have h := P.R1 hx (Function.update 0 i 0) c hw
  rw [P.key_identity, zero_add] at h
  exact h

theorem R2 {x : ∀ i, Q i} (hx : x ∈ P.S) (i : ι) (a c : ZMod p) {w : V} (hw : w ∈ P.W) :
    P.ρ (P.b i (x i) (a + c) * (P.b i (x i) a)⁻¹) w = P.ρ (P.E i (x i) c) w := by
  have h1 := P.R1 hx (Function.update 0 i a) c hw
  rw [P.key_identity] at h1
  rw [← P.R2' hx i c hw, P.rho_mul_apply (P.K x i c), P.rho_mul_apply (P.K x i c)] at h1
  exact P.rho_inj _ h1

theorem R3 {x : ∀ i, Q i} (hx : x ∈ P.S) (i : ι) (c : ZMod p) {w : V} (hw : w ∈ P.W) :
    P.ρ (P.E i (x i) c) w ∈ P.W := by
  refine P.W_B_of_v (P.E_mem _ _ _) ?_ hw
  have hE : P.E i (x i) c = P.Mb x (Function.update 0 i c) * (P.Mb x 0)⁻¹ := by
    rw [P.Mb_eq x i, P.Mb_eq x i 0, P.R_congr x i (β := Function.update 0 i c) (β' := 0)
      (fun j hj => by simp [Function.update_of_ne hj])]
    simp only [Function.update_self, Pi.zero_apply, E]
    group
  rw [hE, P.rho_mul_apply, (P.vA hx 0).1, ← P.rho_mul_apply,
    ← (P.A_comm_B (P.Ma_mem x 0) (P.Mb_mem x _)).eq, P.rho_mul_apply, (P.vA hx _).2,
    ← P.rho_mul_apply]
  exact P.W_A (P.Agrp.mul_mem (P.Ma_mem _ _) (P.Agrp.inv_mem (P.Ma_mem _ _))) P.v_mem

theorem R4 {x : ∀ i, Q i} (hx : x ∈ P.S) (i : ι) (a c : ZMod p) {w : V} (hw : w ∈ P.W) :
    P.ρ (P.E i (x i) (a + c)) w = P.ρ (P.E i (x i) a) (P.ρ (P.E i (x i) c) w) := by
  have h : P.E i (x i) (a + c) = (P.b i (x i) (c + a) * (P.b i (x i) c)⁻¹) * P.E i (x i) c := by
    rw [add_comm a c]; unfold E; group
  rw [h, P.rho_mul_apply, P.R2 hx i c a (P.R3 hx i c hw)]

theorem R6 {x : ∀ i, Q i} (hx : x ∈ P.S) (i : ι) (a : ZMod p) (y' : Q i) (c : ZMod p)
    (hy' : ∀ w ∈ P.W, P.ρ (P.E i y' c) w ∈ P.W) {w : V} (hw : w ∈ P.W) :
    P.ρ (P.E i (x i) a) (P.ρ (P.E i y' c) w) = P.ρ (P.E i y' c) (P.ρ (P.E i (x i) a) w) := by
  apply P.rho_inj (P.K x i a)
  have hKE : Commute (P.K x i a) (P.E i y' c) :=
    (P.K_comm _ _ _ _ _).mul_right (P.K_comm _ _ _ _ _).inv_right
  calc P.ρ (P.K x i a) (P.ρ (P.E i (x i) a) (P.ρ (P.E i y' c) w))
      = P.ρ (P.K x i a * P.E i (x i) a) (P.ρ (P.E i y' c) w) := (P.rho_mul_apply _ _ _).symm
    _ = phase p (a * P.t x) • P.ρ (P.E i y' c) w := P.R2' hx i a (hy' w hw)
    _ = P.ρ (P.E i y' c) (P.ρ (P.K x i a * P.E i (x i) a) w) := by rw [P.R2' hx i a hw, map_smul]
    _ = P.ρ (P.E i y' c * P.K x i a) (P.ρ (P.E i (x i) a) w) := by
      rw [P.rho_mul_apply, P.rho_mul_apply]
    _ = P.ρ (P.K x i a) (P.ρ (P.E i y' c) (P.ρ (P.E i (x i) a) w)) := by
      rw [← hKE.eq, P.rho_mul_apply]

theorem E_comm_ne (i j : ι) (hij : i ≠ j) (y : Q i) (y' : Q j) (a c : ZMod p) :
    Commute (P.E i y a) (P.E j y' c) := by
  unfold E
  apply Commute.mul_left <;> apply Commute.mul_right
  · exact P.hbb _ _ hij _ _ _ _
  · exact (P.hbb _ _ hij _ _ _ _).inv_right
  · exact (P.hbb _ _ hij _ _ _ _).inv_left
  · exact (P.hbb _ _ hij _ _ _ _).inv_left.inv_right

/-! ### Restriction to `W` and the commutative monoid of the `E`'s -/

def good (i : ι) (y : Q i) : Prop := ∃ x ∈ P.S, x i = y

theorem E_inv {i : ι} {y : Q i} (hy : P.good i y) (c : ZMod p) {w : V} (hw : w ∈ P.W) :
    P.ρ (P.E i y c) w ∈ P.W := by
  obtain ⟨x, hx, rfl⟩ := hy
  exact P.R3 hx i c hw

def PW : Submonoid G where
  carrier := {g | ∀ w ∈ P.W, P.ρ g w ∈ P.W}
  mul_mem' := fun {g h} hg hh w hw => by rw [P.rho_mul_apply]; exact hg _ (hh w hw)
  one_mem' := fun w hw => by simpa using hw

def resW : P.PW →* Module.End ℂ P.W where
  toFun g := (P.ρ g.1).restrict g.2
  map_one' := by ext w; simp [LinearMap.restrict_apply]
  map_mul' g h := by ext w; exact P.rho_mul_apply _ _ _

open Classical in
noncomputable def T (i : ι) (y : Q i) (c : ZMod p) : Module.End ℂ P.W :=
  if h : P.good i y then P.resW ⟨P.E i y c, fun _ hw => P.E_inv h c hw⟩ else 1

theorem T_apply {i : ι} {y : Q i} (h : P.good i y) (c : ZMod p) (w : P.W) :
    ((P.T i y c w : P.W) : V) = P.ρ (P.E i y c) w := by
  rw [T, dif_pos h]
  rfl

theorem T_bad {i : ι} {y : Q i} (h : ¬ P.good i y) (c : ZMod p) : P.T i y c = 1 := by
  rw [T, dif_neg h]

theorem T_zero (i : ι) (y : Q i) : P.T i y 0 = 1 := by
  by_cases h : P.good i y
  · apply LinearMap.ext; intro w; apply Subtype.ext
    rw [P.T_apply h, P.E_zero, map_one]
    rfl
  · exact P.T_bad h 0

theorem T_add (i : ι) (y : Q i) (a c : ZMod p) : P.T i y (a + c) = P.T i y a * P.T i y c := by
  by_cases h : P.good i y
  · apply LinearMap.ext; intro w; apply Subtype.ext
    rw [Module.End.mul_apply, P.T_apply h, P.T_apply h, P.T_apply h]
    obtain ⟨x, hx, rfl⟩ := h
    exact P.R4 hx i a c w.2
  · rw [P.T_bad h, P.T_bad h, P.T_bad h, one_mul]

theorem T_comm (i j : ι) (y : Q i) (y' : Q j) (a c : ZMod p) :
    Commute (P.T i y a) (P.T j y' c) := by
  by_cases h : P.good i y
  · by_cases h' : P.good j y'
    · show P.T i y a * P.T j y' c = P.T j y' c * P.T i y a
      apply LinearMap.ext; intro w; apply Subtype.ext
      rw [Module.End.mul_apply, Module.End.mul_apply, P.T_apply h, P.T_apply h', P.T_apply h',
        P.T_apply h]
      by_cases hij : i = j
      · subst hij
        obtain ⟨x, hx, rfl⟩ := h
        exact P.R6 hx i a y' c (fun _ hw => P.E_inv h' c hw) w.2
      · rw [← P.rho_mul_apply, ← P.rho_mul_apply, (P.E_comm_ne i j hij y y' a c).eq]
    · rw [P.T_bad h']; exact Commute.one_right _
  · rw [P.T_bad h]; exact Commute.one_left _

def gens : Set (Module.End ℂ P.W) :=
  Set.range (fun z : (Σ i, Q i) × ZMod p => P.T z.1.1 z.1.2 z.2) ∪
    Set.range (algebraMap ℂ (Module.End ℂ P.W))

theorem gens_comm : ∀ a ∈ P.gens, ∀ b ∈ P.gens, a * b = b * a := by
  rintro _ (⟨z, rfl⟩ | ⟨c, rfl⟩) _ (⟨z', rfl⟩ | ⟨c', rfl⟩)
  · exact (P.T_comm _ _ _ _ _ _).eq
  · exact (Algebra.commutes _ _).symm
  · exact Algebra.commutes _ _
  · exact Algebra.commutes _ _

theorem ncp_T {x : ∀ i, Q i} (hx : x ∈ P.S) (γ : ZMod p) (s : Finset ι) (w : P.W) :
    ((s.noncommProd (fun i => P.T i (x i) γ) (pw (fun i j _ => P.T_comm i j _ _ γ γ) s) w : P.W) : V)
      = P.ρ (s.noncommProd (fun i => P.E i (x i) γ)
          (pw (fun i j h => P.E_comm_ne i j h _ _ γ γ) s)) w := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [noncommProd_insert_of_notMem _ _ _ _ ha, noncommProd_insert_of_notMem _ _ _ _ ha,
      Module.End.mul_apply, P.T_apply ⟨x, hx, rfl⟩, ih, ← P.rho_mul_apply]

theorem prod_T {x : ∀ i, Q i} (hx : x ∈ P.S) (γ : ZMod p) (w : P.W) :
    ((univ.noncommProd (fun i => P.T i (x i) γ) (pw (fun i j _ => P.T_comm i j _ _ γ γ) univ) w
      : P.W) : V) = phase p (γ * P.t x) • (w : V) := by
  rw [P.ncp_T hx γ univ w]
  have h1 : univ.noncommProd (fun i => P.E i (x i) γ)
      (pw (fun i j h => P.E_comm_ne i j h _ _ γ γ) univ)
      = P.Mb x (fun _ => γ) * (P.Mb x 0)⁻¹ :=
    (ncp_mul_inv univ (fun i => P.b i (x i) γ) (fun i => P.b i (x i) 0)
      (fun i j h => P.hbb i j h _ _ _ _) (fun i j h => P.hbb i j h _ _ _ _)
      (fun i j h => P.hbb i j h _ _ _ _)).symm
  have h2 : P.Mb x (fun _ => γ) = P.Mb x (fun i => (0 : ι → ZMod p) i + γ) := by
    congr 1; funext i; simp
  rw [h1, h2]
  exact P.R1 hx 0 γ w.2

open Classical in
theorem core {K : Type*} [Fintype K] (xs : K → ∀ i, Q i) (hxs : ∀ k, xs k ∈ P.S) (c : K → ZMod p)
    (hmarg : ∀ i (y : Q i), ∑ k ∈ univ.filter (fun k => xs k i = y), c k = 0) :
    ∑ k, c k * P.t (xs k) = 0 := by
  classical
  let N := Submonoid.closure P.gens
  letI : CommMonoid N := Submonoid.closureCommMonoidOfComm _ P.gens_comm
  let Th : ∀ i, Q i → Multiplicative (ZMod p) →* N := fun i y =>
    { toFun := fun c => ⟨P.T i y c.toAdd, Submonoid.subset_closure (Or.inl ⟨(⟨i, y⟩, c.toAdd), rfl⟩)⟩
      map_one' := Subtype.ext (P.T_zero i y)
      map_mul' := fun a b => Subtype.ext (P.T_add i y a.toAdd b.toAdd) }
  let sc : Multiplicative (ZMod p) →* N :=
    { toFun := fun c => ⟨algebraMap ℂ (Module.End ℂ P.W) (phase p c.toAdd),
        Submonoid.subset_closure (Or.inr ⟨_, rfl⟩)⟩
      map_one' := Subtype.ext (by
        show algebraMap ℂ (Module.End ℂ P.W) (phase p 0) = 1
        rw [phase_zero, map_one])
      map_mul' := fun a b => Subtype.ext (by
        show algebraMap ℂ (Module.End ℂ P.W) (phase p (a.toAdd + b.toAdd)) =
          algebraMap ℂ (Module.End ℂ P.W) (phase p a.toAdd) *
            algebraMap ℂ (Module.End ℂ P.W) (phase p b.toAdd)
        rw [phase_add, map_mul]) }
  have hrel : ∀ k (γ : ZMod p),
      ∏ i, Th i (xs k i) (Multiplicative.ofAdd γ) = sc (Multiplicative.ofAdd (γ * P.t (xs k))) := by
    intro k γ
    apply Subtype.ext
    have e : ((∏ i, Th i (xs k i) (Multiplicative.ofAdd γ) : N) : Module.End ℂ P.W) =
        univ.noncommProd (fun i => P.T i (xs k i) γ) (pw (fun i j _ => P.T_comm i j _ _ γ γ) univ) := by
      rw [← Finset.noncommProd_eq_prod]
      exact Finset.map_noncommProd _ _ _ N.subtype
    rw [e]
    apply LinearMap.ext; intro w; apply Subtype.ext
    rw [P.prod_T (hxs k) γ w]
    show _ = ((algebraMap ℂ (Module.End ℂ P.W) (phase p (γ * P.t (xs k))) w : P.W) : V)
    rw [Module.algebraMap_end_apply]
    rfl
  have hone : sc (Multiplicative.ofAdd (∑ k, c k * P.t (xs k))) = 1 := by
    rw [ofAdd_sum, map_prod]
    simp_rw [← hrel]
    rw [Finset.prod_comm]
    apply Finset.prod_eq_one
    intro i _
    rw [← Finset.prod_fiberwise_of_maps_to (t := univ.image (fun k => xs k i))
      (g := fun k => xs k i) (fun k _ => mem_image_of_mem _ (mem_univ k))]
    apply Finset.prod_eq_one
    intro y _
    rw [Finset.prod_congr rfl (fun k hk => by rw [(mem_filter.1 hk).2]), ← map_prod, ← ofAdd_sum,
      hmarg i y, ofAdd_zero, map_one]
  have h2 := congrArg (fun n : N => ((n : Module.End ℂ P.W) ⟨P.v, P.v_mem⟩ : V)) hone
  simp only [sc, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, Module.algebraMap_end_apply] at h2
  have h3 : (phase p (∑ k, c k * P.t (xs k)) - 1) • P.v = 0 := by
    rw [sub_smul, one_smul]
    exact sub_eq_zero.mpr (by simpa using h2)
  rcases smul_eq_zero.mp h3 with h4 | h4
  · exact phase_eq_one (sub_eq_zero.mp h4)
  · exact absurd h4 P.hv

end Setup

end XorParallelRepetition.Dev.BlrNoEmb
end

section
set_option autoImplicit false

namespace XorParallelRepetition.Dev.BlrNoEmb

open XorParallelRepetition.Exponential Finset


/-! ### A perfect classical strategy on every finite set of questions gives value one -/

theorem winProb_le_one' {ι : Type} (G : Game ι) (S : G.Strategy) : G.winProb S ≤ 1 := by
  unfold Game.winProb
  calc G.law.toOuterMeasure _ ≤ G.law.toOuterMeasure Set.univ :=
        PMF.toOuterMeasure_mono _ (fun _ _ => trivial)
    _ = 1 := by rw [PMF.toOuterMeasure_apply_eq_one_iff]; exact Set.subset_univ _

theorem val_eq_one {p : ℕ} {ι : Type} [Fintype ι] (Ψ : XorGame.{u} p ι)
    (h : ∀ F : Finset (∀ i, Ψ.Q i), (∀ x ∈ F, x ∈ Ψ.μ.support) →
      ∃ σ : ∀ i, Ψ.Q i → ZMod p, ∀ x ∈ F, ∑ i, σ i (x i) = Ψ.t x) :
    Ψ.val = 1 := by
  classical
  unfold XorGame.val GeneralizedXorGame.val Game.val
  suffices hs : (⨆ S, Ψ.toGeneralized.toGame.winProb S) = 1 by rw [hs]; rfl
  apply le_antisymm (iSup_le fun S => winProb_le_one' _ S)
  rw [← PMF.tsum_coe Ψ.μ, ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun F => ?_
  obtain ⟨σ, hσ⟩ := h (F.filter (· ∈ Ψ.μ.support)) (fun x hx => (mem_filter.1 hx).2)
  refine le_iSup_of_le (σ : Ψ.toGeneralized.toGame.Strategy) ?_
  have e : Ψ.toGeneralized.toGame.winProb σ =
      Ψ.μ.toOuterMeasure {x | ∑ i, σ i (x i) = Ψ.t x} := by
    unfold Game.winProb
    exact PMF.toOuterMeasure_map_apply _ _ _
  rw [e, PMF.toOuterMeasure_apply]
  calc ∑ x ∈ F, Ψ.μ x = ∑ x ∈ F, Set.indicator {x | ∑ i, σ i (x i) = Ψ.t x} Ψ.μ x := by
        refine sum_congr rfl fun x hx => ?_
        by_cases hs : x ∈ Ψ.μ.support
        · rw [Set.indicator_of_mem]
          exact hσ x (mem_filter.2 ⟨hx, hs⟩)
        · rw [PMF.mem_support_iff, not_not] at hs
          simp [Set.indicator_apply, hs]
    _ ≤ _ := ENNReal.sum_le_tsum _

/-! ### Linear algebra over `F_p`: a finite system without a contradiction is solvable -/

open Classical in
theorem solvable {K : Type*} [Field K] {ι : Type} [Fintype ι] {Q : ι → Type*}
    (t : (∀ i, Q i) → K) (F : Finset (∀ i, Q i))
    (hcore : ∀ c : F → K,
      (∀ i (y : Q i), ∑ k ∈ univ.filter (fun k : F => (k : ∀ i, Q i) i = y), c k = 0) →
      ∑ k : F, c k * t k = 0) :
    ∃ σ : ∀ i, Q i → K, ∀ x ∈ F, ∑ i, σ i (x i) = t x := by
  let L : (∀ i, Q i → K) →ₗ[K] (F → K) :=
    { toFun := fun σ k => ∑ i, σ i ((k : ∀ i, Q i) i)
      map_add' := by intro σ τ; funext k; simp [Finset.sum_add_distrib]
      map_smul' := by intro a σ; funext k; simp [Finset.mul_sum] }
  by_cases ht : (fun k : F => t k) ∈ LinearMap.range L
  · obtain ⟨σ, hσ⟩ := ht
    exact ⟨σ, fun x hx => congrFun hσ ⟨x, hx⟩⟩
  exfalso
  obtain ⟨f, hf, hfL⟩ := Submodule.exists_dual_map_eq_bot_of_notMem ht
    (Module.Projective.of_free (R := K))
  let c : F → K := fun k => f (fun j => if k = j then 1 else 0)
  have hf_eq : ∀ g : F → K, f g = ∑ k, g k * c k := by
    intro g
    conv_lhs => rw [pi_eq_sum_univ g]
    rw [map_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [map_smul, smul_eq_mul]
  have hfL0 : ∀ σ, f (L σ) = 0 := by
    intro σ
    have hm : f (L σ) ∈ (LinearMap.range L).map f := ⟨L σ, ⟨σ, rfl⟩, rfl⟩
    rw [hfL] at hm
    exact (Submodule.mem_bot K).mp hm
  apply hf
  rw [hf_eq]
  have := hcore c (fun i y => by
    have h0 := hfL0 (Pi.single i (fun z : Q i => if z = y then 1 else 0))
    rw [hf_eq] at h0
    rw [Finset.sum_filter]
    refine Eq.trans (sum_congr rfl fun k _ => ?_) h0
    have hL : L (Pi.single i (fun z : Q i => if z = y then 1 else 0)) k =
        if (k : ∀ i, Q i) i = y then 1 else 0 := by
      show ∑ j, Pi.single (M := fun j => Q j → K) i (fun z : Q i => if z = y then (1 : K) else 0) j
        ((k : ∀ i, Q i) j) = _
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        rw [Pi.single_eq_of_ne hj]
        rfl
      · intro hi; exact absurd (mem_univ i) hi
    rw [hL]
    split_ifs <;> simp)
  rw [← this]
  exact sum_congr rfl fun k _ => mul_comm _ _

/-! ### Splitting a commuting product over `ι × Bool` -/

theorem split_prod {M : Type*} [Monoid M] {ι : Type} [Fintype ι] (f : ι × Bool → M)
    (hf : ∀ s t, s ≠ t → Commute (f s) (f t)) :
    univ.noncommProd f (pw hf univ) =
      univ.noncommProd (fun i => f (i, true))
          (pw (fun i j h => hf _ _ (by simp [h])) univ) *
        univ.noncommProd (fun i => f (i, false))
          (pw (fun i j h => hf _ _ (by simp [h])) univ) := by
  classical
  let C := Submonoid.closure (Set.range f)
  have hC : ∀ a ∈ Set.range f, ∀ b ∈ Set.range f, a * b = b * a := by
    rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
    by_cases hst : s = t
    · rw [hst]
    · exact (hf s t hst).eq
  letI : CommMonoid C := Submonoid.closureCommMonoidOfComm _ hC
  let F : ι × Bool → C := fun s => ⟨f s, Submonoid.subset_closure ⟨s, rfl⟩⟩
  have key : ∀ {κ : Type} (g : κ → ι × Bool) (s : Finset κ) (h),
      s.noncommProd (fun k => f (g k)) h = ((∏ k ∈ s, F (g k) : C) : M) := by
    intro κ g s h
    rw [← Finset.noncommProd_eq_prod]
    exact (Finset.map_noncommProd s (fun k => F (g k)) (fun _ _ _ _ _ => Commute.all _ _)
      C.subtype).symm
  calc univ.noncommProd f (pw hf univ) = ((∏ s, F s : C) : M) := key id univ _
    _ = (((∏ i, F (i, true)) * (∏ i, F (i, false)) : C) : M) := by
        rw [Fintype.prod_prod_type, ← Finset.prod_mul_distrib]
        simp only [Fintype.prod_bool]
    _ = _ := by
        rw [Submonoid.coe_mul, ← key (fun i => (i, true)), ← key (fun i => (i, false))]

/-! ### The data of a commuting embedding of `Ψ′` -/

section Embedding

variable {p : ℕ} [Fact p.Prime] {ι : Type} [Fintype ι] [DecidableEq ι] (Ψ : XorGame.{u} p ι)
  {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  (E : CommutingEmbedding Ψ.blr V)

/-- The operator `U_s(q)` as an element of the unitary group. -/
def uop (s : ι × Bool) (q : Ψ.Q s.1 × ZMod p) : unitary (V →L[ℂ] V) :=
  ⟨E.U s q, E.unitary_mem s q⟩

theorem uop_comm (s t : ι × Bool) (hst : s ≠ t) (q : Ψ.Q s.1 × ZMod p) (q' : Ψ.Q t.1 × ZMod p) :
    Commute (uop Ψ E s q) (uop Ψ E t q') :=
  Subtype.ext (E.commute s t hst q q').eq

noncomputable def rhoU : unitary (V →L[ℂ] V) →* Module.End ℂ V :=
  (ContinuousLinearMap.toLinearMapRingHom : (V →L[ℂ] V) →+* Module.End ℂ V).toMonoidHom.comp
    (unitary (V →L[ℂ] V)).subtype

theorem blrChallenge_mem {x : ∀ i, Ψ.Q i} (hx : x ∈ Ψ.μ.support) (γ : ZMod p)
    (α : ι → ZMod p) : Ψ.blrChallenge x γ α ∈ Ψ.blr.μ.support := by
  have : Ψ.blrChallenge x γ α ∈ (Ψ.μ.bind fun x => (PMF.uniformOfFintype (ZMod p)).bind fun γ =>
      (PMF.uniformOfFintype (ι → ZMod p)).map fun α => Ψ.blrChallenge x γ α).support := ?_
  · exact this
  rw [PMF.mem_support_bind_iff]
  refine ⟨x, hx, ?_⟩
  rw [PMF.mem_support_bind_iff]
  refine ⟨γ, PMF.mem_support_uniformOfFintype _, ?_⟩
  rw [PMF.mem_support_map_iff]
  exact ⟨α, PMF.mem_support_uniformOfFintype _, rfl⟩

noncomputable def setupOf : Setup ι Ψ.Q p (unitary (V →L[ℂ] V)) V where
  ρ := rhoU
  a i y c := uop Ψ E (i, false) (y, c)
  b i y c := uop Ψ E (i, true) (y, c)
  hab i j y y' c c' := uop_comm Ψ E _ _ (by simp) _ _
  haa i j h y y' c c' := uop_comm Ψ E _ _ (by simp [h]) _ _
  hbb i j h y y' c c' := uop_comm Ψ E _ _ (by simp [h]) _ _
  S := Ψ.μ.support
  t := Ψ.t
  v := E.v
  hv := E.v_ne_zero
  heig x hx α γ := by
    have h := E.eigen _ (blrChallenge_mem Ψ hx γ α)
    have hsplit := split_prod (fun s => uop Ψ E s ((Ψ.blrChallenge x γ α).1 s))
      (fun s t hst => uop_comm Ψ E s t hst _ _)
    have hmap := Finset.map_noncommProd univ (fun s => uop Ψ E s ((Ψ.blrChallenge x γ α).1 s))
      (pw (fun s t hst => uop_comm Ψ E s t hst _ _) univ) (unitary (V →L[ℂ] V)).subtype
    have e : (univ.noncommProd (fun s => E.U s ((Ψ.blrChallenge x γ α).1 s))
        (fun s _ t _ hst => E.commute s t hst _ _)) =
        ((mprod (fun i y c => uop Ψ E (i, true) (y, c)) (fun i j h y y' c c' =>
            uop_comm Ψ E _ _ (by simp [h]) _ _) x (fun i => α i + γ) *
          mprod (fun i y c => uop Ψ E (i, false) (y, c)) (fun i j h y y' c c' =>
            uop_comm Ψ E _ _ (by simp [h]) _ _) x α : unitary (V →L[ℂ] V)) : V →L[ℂ] V) := by
      calc _ = (unitary (V →L[ℂ] V)).subtype (univ.noncommProd
            (fun s => uop Ψ E s ((Ψ.blrChallenge x γ α).1 s))
            (pw (fun s t hst => uop_comm Ψ E s t hst _ _) univ)) := hmap.symm
        _ = _ := by rw [hsplit]; rfl
    rw [e] at h
    exact h

end Embedding

end XorParallelRepetition.Dev.BlrNoEmb

namespace XorParallelRepetition.Exponential


open XorParallelRepetition.Dev.BlrNoEmb in
theorem chk_blr_no_commuting_embedding {p : ℕ} [Fact p.Prime] {ι : Type} [Fintype ι] [DecidableEq ι]
    (Ψ : XorGame.{u} p ι) (hval : Ψ.val < 1) :
    ¬ HasCommutingEmbedding Ψ.blr := by
  rintro ⟨V, _, _, _, ⟨E⟩⟩
  have h1 : Ψ.val = 1 := val_eq_one Ψ fun F hF =>
    solvable Ψ.t F fun c hmarg =>
      (setupOf Ψ E).core (fun k : F => (k : ∀ i, Ψ.Q i)) (fun k => hF k k.2) c hmarg
  rw [h1] at hval
  exact lt_irrefl _ hval

end XorParallelRepetition.Exponential
end

theorem solution : type_of% @XorParallelRepetition.Exponential.chk_blr_no_commuting_embedding := @XorParallelRepetition.Exponential.chk_blr_no_commuting_embedding
