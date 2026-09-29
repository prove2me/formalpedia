-- Prove2me | solution 1 for Representation.nonempty_equiv_torsionBy_quotient_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/f9038e94-39f8-5af7-9cb4-168c70732d5a

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Representation_nonempty_equiv_torsionBy_quotient_of_coprime

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module"
open scoped Classical TensorProduct Pointwise

namespace TorsRed

section Compl

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

omit [Finite G] in

theorem exists_compl_addSubgroup [Finite G] [NeZero ((Nat.card G : ℕ) : ZMod p)] {M : Type} [AddCommGroup M] [Module (ZMod p) M]
    (τ : Representation (ZMod p) G M) (W : AddSubgroup M) (hW : ∀ g, ∀ x ∈ W, τ g x ∈ W) :
    ∃ W' : AddSubgroup M, (∀ g, ∀ x ∈ W', τ g x ∈ W') ∧ (∀ x, x ∈ W → x ∈ W' → x = 0) ∧ (∀ x, ∃ y ∈ W, ∃ z ∈ W', x = y + z) := by
  have hss : Representation.IsSemisimpleRepresentation τ := MonoidAlgebra.Submodule.instIsSemisimpleRepresentation τ
  obtain ⟨Wc, hWc⟩ := hss.exists_isCompl (⟨(AddSubgroup.toZModSubmodule p) W, fun g v hv => hW g v hv⟩ : Subrepresentation τ)
  refine ⟨Wc.toSubmodule.toAddSubgroup, fun g x hx => Wc.apply_mem_toSubmodule g hx, fun x hxW hxW' => ?_, fun x => ?_⟩
  · have hx : x ∈ (⟨(AddSubgroup.toZModSubmodule p) W, fun g v hv => hW g v hv⟩ : Subrepresentation τ) ⊓ Wc := ⟨hxW, hxW'⟩
    rw [hWc.inf_eq_bot] at hx
    exact hx
  · have hx : x ∈ (⟨(AddSubgroup.toZModSubmodule p) W, fun g v hv => hW g v hv⟩ : Subrepresentation τ) ⊔ Wc := by
      rw [hWc.sup_eq_top]; trivial
    rw [← SetLike.mem_coe, Subrepresentation.coe_sup] at hx
    obtain ⟨y, hy, z, hz, rfl⟩ := hx
    exact ⟨y, hy, z, hz, rfl⟩

noncomputable def toZMod (p : ℕ) {M : Type} [AddCommGroup M] [Module (ZMod p) M] {inst : Module ℤ M} (σ : @Representation ℤ G M _ _ _ inst) :
    Representation (ZMod p) G M where
  toFun g := (σ g).toAddMonoidHom.toZModLinearMap p
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

omit [Finite G] [Fact p.Prime] in
theorem toZMod_apply (p : ℕ) {M : Type} [AddCommGroup M] [Module (ZMod p) M] {inst : Module ℤ M} (σ : @Representation ℤ G M _ _ _ inst)
    (g : G) (m : M) : toZMod p σ g m = σ g m := rfl

theorem exists_isCompl_of_coprime (hG : (Nat.card G).Coprime p) {M : Type} [AddCommGroup M] {inst : Module ℤ M}
    (σ : @Representation ℤ G M _ _ _ inst) (hM : ∀ m : M, p • m = 0)
    (W : @Submodule ℤ M _ _ inst) (hW : ∀ g, W ≤ W.comap (σ g)) :
    ∃ W' : @Submodule ℤ M _ _ inst, (∀ g, W' ≤ W'.comap (σ g)) ∧ IsCompl W W' := by
  haveI : NeZero ((Nat.card G : ℕ) : ZMod p) := ⟨by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => (Nat.Prime.coprime_iff_not_dvd (Fact.out)).1 (Nat.Coprime.symm hG) h⟩
  obtain ⟨W', h1, h2, h3⟩ := @exists_compl_addSubgroup G _ p _ _ _ M _ (AddCommGroup.zmodModule hM)
    (@toZMod G _ p M _ (AddCommGroup.zmodModule hM) inst σ) W.toAddSubgroup (fun g x hx => hW g hx)
  refine ⟨{ carrier := W', add_mem' := fun ha hb => W'.add_mem ha hb, zero_mem' := W'.zero_mem,
            smul_mem' := fun c x hx => by
              change inst.smul c x ∈ W'
              rw [int_smul_eq_zsmul]
              exact W'.zsmul_mem hx c }, fun g x hx => h1 g x hx, ?_⟩
  constructor
  · rw [disjoint_iff, eq_bot_iff]
    intro x hx
    exact (Submodule.mem_bot ℤ).2 (h2 x hx.1 hx.2)
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    obtain ⟨y, hy, z, hz, rfl⟩ := h3 x
    exact Submodule.add_mem_sup hy hz

end Compl

end TorsRed

namespace TorsRed

section Generic

variable {k G : Type} [CommRing k] [Group G]

noncomputable def equivOfSubsingleton {V V' : Type} [AddCommGroup V] [AddCommGroup V'] {iV : Module k V} {iV' : Module k V'}
    (ρ : Representation k G V) (ρ' : Representation k G V') [Subsingleton V] [Subsingleton V'] : ρ.Equiv ρ' :=
  Representation.Equiv.mk
    { toFun := 0, invFun := 0, map_add' := fun _ _ => Subsingleton.elim _ _, map_smul' := fun _ _ => Subsingleton.elim _ _,
      left_inv := fun _ => Subsingleton.elim _ _, right_inv := fun _ => Subsingleton.elim _ _ }
    (fun _ => LinearMap.ext fun _ => Subsingleton.elim _ _)

theorem nonempty_equiv_of_isCompl {V V' : Type} [AddCommGroup V] [AddCommGroup V'] {iV : Module k V} {iV' : Module k V'}
    (ρ : Representation k G V) (ρ' : Representation k G V')
    (W₁ W₂ : Submodule k V) (h₁ : ∀ g, W₁ ≤ W₁.comap (ρ g)) (h₂ : ∀ g, W₂ ≤ W₂.comap (ρ g)) (hc : IsCompl W₁ W₂)
    (W₁' W₂' : Submodule k V') (h₁' : ∀ g, W₁' ≤ W₁'.comap (ρ' g)) (h₂' : ∀ g, W₂' ≤ W₂'.comap (ρ' g)) (hc' : IsCompl W₁' W₂')
    (e₁ : (ρ.subrepresentation W₁ h₁).Equiv (ρ'.subrepresentation W₁' h₁'))
    (e₂ : (ρ.subrepresentation W₂ h₂).Equiv (ρ'.subrepresentation W₂' h₂')) :
    Nonempty (ρ.Equiv ρ') := by
  let E : V ≃ₗ[k] V' :=
    (Submodule.prodEquivOfIsCompl W₁ W₂ hc).symm ≪≫ₗ (e₁.toLinearEquiv.prodCongr e₂.toLinearEquiv) ≪≫ₗ
      Submodule.prodEquivOfIsCompl W₁' W₂' hc'
  have hE : ∀ (a : W₁) (b : W₂), E ((a : V) + (b : V)) = (e₁ a : V') + (e₂ b : V') := fun a b => by
    have : (a : V) + (b : V) = Submodule.prodEquivOfIsCompl W₁ W₂ hc (a, b) := (Submodule.coe_prodEquivOfIsCompl' _ _ hc (a, b)).symm
    rw [this]
    change Submodule.prodEquivOfIsCompl W₁' W₂' hc' ((e₁.toLinearEquiv.prodCongr e₂.toLinearEquiv)
      ((Submodule.prodEquivOfIsCompl W₁ W₂ hc).symm (Submodule.prodEquivOfIsCompl W₁ W₂ hc (a, b)))) = _
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.prodCongr_apply, Submodule.coe_prodEquivOfIsCompl']
    rfl
  refine ⟨Representation.Equiv.mk E fun g => LinearMap.ext fun v => ?_⟩
  obtain ⟨⟨a, b⟩, rfl⟩ := (Submodule.prodEquivOfIsCompl W₁ W₂ hc).surjective v
  rw [Submodule.coe_prodEquivOfIsCompl']
  change E (ρ g ((a : V) + (b : V))) = ρ' g (E ((a : V) + (b : V)))
  have ha : ρ g (a : V) = ((ρ.subrepresentation W₁ h₁ g a : W₁) : V) := rfl
  have hb : ρ g (b : V) = ((ρ.subrepresentation W₂ h₂ g b : W₂) : V) := rfl
  rw [map_add, ha, hb, hE, hE, map_add]
  have h1 := Representation.IntertwiningMap.isIntertwining _ _ e₁.toIntertwiningMap g a
  have h2 := Representation.IntertwiningMap.isIntertwining _ _ e₂.toIntertwiningMap g b
  simp only [Representation.Equiv.coe_toIntertwiningMap] at h1 h2
  rw [h1, h2]
  rfl

theorem nonempty_equiv_range_of_isCompl_ker {M N : Type} [AddCommGroup M] [AddCommGroup N] {iM : Module k M} {iN : Module k N}
    (ρ : Representation k G M) (σ : Representation k G N) (φ : M →ₗ[k] N) (hφ : ∀ g (m : M), φ (ρ g m) = σ g (φ m))
    (C : Submodule k M) (hC : ∀ g, C ≤ C.comap (ρ g)) (hc : IsCompl (LinearMap.ker φ) C)
    (hR : ∀ g, LinearMap.range φ ≤ (LinearMap.range φ).comap (σ g)) :
    Nonempty ((ρ.subrepresentation C hC).Equiv (σ.subrepresentation (LinearMap.range φ) hR)) := by
  let ψ : C →ₗ[k] LinearMap.range φ := (φ ∘ₗ C.subtype).codRestrict _ (fun c => ⟨c, rfl⟩)
  have hinj : Function.Injective ψ := by
    intro x y hxy
    have h : φ (x : M) = φ (y : M) := congrArg Subtype.val hxy
    have hk : (x : M) - (y : M) ∈ LinearMap.ker φ := by rw [LinearMap.mem_ker, map_sub, h, sub_self]
    have hC' : (x : M) - (y : M) ∈ C := C.sub_mem x.2 y.2
    have hmem : (x : M) - (y : M) ∈ LinearMap.ker φ ⊓ C := ⟨hk, hC'⟩
    rw [hc.inf_eq_bot] at hmem
    have h0 : (x : M) - (y : M) = 0 := (Submodule.mem_bot k).1 hmem
    exact Subtype.ext (sub_eq_zero.1 h0)
  have hsurj : Function.Surjective ψ := by
    rintro ⟨_, m, rfl⟩
    obtain ⟨⟨a, b⟩, rfl⟩ := (Submodule.prodEquivOfIsCompl _ _ hc).surjective m
    refine ⟨b, Subtype.ext ?_⟩
    change φ (b : M) = φ (Submodule.prodEquivOfIsCompl _ _ hc (a, b))
    rw [Submodule.coe_prodEquivOfIsCompl', map_add, LinearMap.mem_ker.1 a.2, zero_add]
  refine ⟨Representation.Equiv.mk (LinearEquiv.ofBijective ψ ⟨hinj, hsurj⟩) fun g => LinearMap.ext fun c => Subtype.ext ?_⟩
  exact hφ g (c : M)

theorem nonempty_equiv_of_isCompl_ker_of_surjective {M N : Type} [AddCommGroup M] [AddCommGroup N] {iM : Module k M} {iN : Module k N}
    (ρ : Representation k G M) (σ : Representation k G N) (φ : M →ₗ[k] N) (hφ : ∀ g (m : M), φ (ρ g m) = σ g (φ m))
    (C : Submodule k M) (hC : ∀ g, C ≤ C.comap (ρ g)) (hc : IsCompl (LinearMap.ker φ) C) (hs : Function.Surjective φ) :
    Nonempty ((ρ.subrepresentation C hC).Equiv σ) := by
  let ψ : C →ₗ[k] N := φ ∘ₗ C.subtype
  have hinj : Function.Injective ψ := by
    intro x y hxy
    have h : φ (x : M) = φ (y : M) := hxy
    have hk : (x : M) - (y : M) ∈ LinearMap.ker φ := by rw [LinearMap.mem_ker, map_sub, h, sub_self]
    have hC' : (x : M) - (y : M) ∈ C := C.sub_mem x.2 y.2
    have hmem : (x : M) - (y : M) ∈ LinearMap.ker φ ⊓ C := ⟨hk, hC'⟩
    rw [hc.inf_eq_bot] at hmem
    have h0 : (x : M) - (y : M) = 0 := (Submodule.mem_bot k).1 hmem
    exact Subtype.ext (sub_eq_zero.1 h0)
  have hsurj : Function.Surjective ψ := by
    intro n
    obtain ⟨m, rfl⟩ := hs n
    obtain ⟨⟨a, b⟩, rfl⟩ := (Submodule.prodEquivOfIsCompl _ _ hc).surjective m
    refine ⟨b, ?_⟩
    change φ (b : M) = φ (Submodule.prodEquivOfIsCompl _ _ hc (a, b))
    rw [Submodule.coe_prodEquivOfIsCompl', map_add, LinearMap.mem_ker.1 a.2, zero_add]
  refine ⟨Representation.Equiv.mk (LinearEquiv.ofBijective ψ ⟨hinj, hsurj⟩) fun g => LinearMap.ext fun c => ?_⟩
  exact hφ g (c : M)

theorem torsionBy_le_comap {M : Type} [AddCommGroup M] {iM : Module k M} (ρ : Representation k G M) (a : k) (g : G) :
    Submodule.torsionBy k M a ≤ (Submodule.torsionBy k M a).comap (ρ g) := fun x hx => by
  rw [Submodule.mem_comap, Submodule.mem_torsionBy_iff, ← map_smul]
  rw [Submodule.mem_torsionBy_iff] at hx
  rw [hx, map_zero]

open scoped Pointwise in

theorem smul_top_le_comap {M : Type} [AddCommGroup M] {iM : Module k M} (ρ : Representation k G M) (a : k) (g : G) :
    (a • (⊤ : Submodule k M)) ≤ (a • (⊤ : Submodule k M)).comap (ρ g) := fun x hx => by
  rw [Submodule.mem_comap]
  obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
  rw [map_smul]
  exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top

end Generic

end TorsRed

namespace TorsRed

section Main

open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

omit [Finite G] [Fact p.Prime] in

theorem nonempty_equiv_e₁ {A : Type} [AddCommGroup A] (ρ : Representation ℤ G A)
    (hT : ∀ g, Submodule.torsionBy ℤ A (p : ℤ) ≤ (Submodule.torsionBy ℤ A (p : ℤ)).comap (ρ g))
    (hP : ∀ g, ((p : ℤ) • (⊤ : Submodule ℤ A)) ≤ ((p : ℤ) • (⊤ : Submodule ℤ A)).comap (ρ g))
    (hW₁ : ∀ g, ((p : ℤ) • (⊤ : Submodule ℤ A)).comap (Submodule.torsionBy ℤ A (p : ℤ)).subtype ≤
      (((p : ℤ) • (⊤ : Submodule ℤ A)).comap (Submodule.torsionBy ℤ A (p : ℤ)).subtype).comap (ρ.subrepresentation _ hT g))
    (hTB : ∀ g, Submodule.torsionBy ℤ ↥((p : ℤ) • (⊤ : Submodule ℤ A)) (p : ℤ) ≤
      (Submodule.torsionBy ℤ ↥((p : ℤ) • (⊤ : Submodule ℤ A)) (p : ℤ)).comap (ρ.subrepresentation _ hP g)) :
    Nonempty (((ρ.subrepresentation _ hT).subrepresentation _ hW₁).Equiv ((ρ.subrepresentation _ hP).subrepresentation _ hTB)) := by
  refine ⟨Representation.Equiv.mk
    { toFun := fun x => ⟨⟨((x : Submodule.torsionBy ℤ A (p : ℤ)) : A), x.2⟩, ?_⟩
      invFun := fun y => ⟨⟨((y : ↥((p : ℤ) • (⊤ : Submodule ℤ A))) : A), ?_⟩, y.1.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl } fun g => LinearMap.ext fun _ => rfl⟩
  · rw [Submodule.mem_torsionBy_iff]
    apply Subtype.ext
    have hx := (Submodule.mem_torsionBy_iff _ _).1 (x : Submodule.torsionBy ℤ A (p : ℤ)).2
    exact hx
  · rw [Submodule.mem_torsionBy_iff]
    have hy := congrArg Subtype.val ((Submodule.mem_torsionBy_iff _ _).1 y.2)
    exact hy

noncomputable def mulp (p : ℕ) (A : Type) [AddCommGroup A] : A →ₗ[ℤ] ↥((p : ℤ) • (⊤ : Submodule ℤ A)) :=
  LinearMap.codRestrict _ ((p : ℤ) • LinearMap.id) (fun a => Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top)

omit [Finite G] [Fact p.Prime] in
theorem mulp_apply_coe {A : Type} [AddCommGroup A] (a : A) : ((mulp p A a : ↥((p : ℤ) • (⊤ : Submodule ℤ A))) : A) = (p : ℤ) • a := rfl

theorem main (hG : (Nat.card G).Coprime p) (n : ℕ) : ∀ (A : Type) [AddCommGroup A] [Finite A] (ρ : Representation ℤ G A)
    (h1 : ∀ g, Submodule.torsionBy ℤ A (p : ℤ) ≤ (Submodule.torsionBy ℤ A (p : ℤ)).comap (ρ g))
    (h2 : ∀ g, ((p : ℤ) • (⊤ : Submodule ℤ A)) ≤ ((p : ℤ) • (⊤ : Submodule ℤ A)).comap (ρ g)),
    Nat.card A = n → Nonempty ((ρ.subrepresentation _ h1).Equiv (ρ.quotient _ h2)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A _ _ ρ h1 h2 hn

  set T : Submodule ℤ A := Submodule.torsionBy ℤ A (p : ℤ) with hTdef
  set P : Submodule ℤ A := (p : ℤ) • (⊤ : Submodule ℤ A) with hPdef
  have hp0 : ∀ a : A, p • a ∈ P := fun a => by
    rw [← natCast_zsmul]; exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
  by_cases htop : P = ⊤
  ·
    have hsurj : Function.Surjective (fun a : A => (p : ℤ) • a) := fun b => by
      have hb : b ∈ P := htop ▸ Submodule.mem_top
      obtain ⟨a, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hb
      exact ⟨a, rfl⟩
    have hinj : Function.Injective (fun a : A => (p : ℤ) • a) := Finite.injective_iff_surjective.2 hsurj
    haveI : Subsingleton T := ⟨fun x y => Subtype.ext (hinj (by
      have hx := (Submodule.mem_torsionBy_iff (p : ℤ) (x : A)).1 x.2
      have hy := (Submodule.mem_torsionBy_iff (p : ℤ) (y : A)).1 y.2
      change (p : ℤ) • (x : A) = (p : ℤ) • (y : A)
      rw [hx, hy]))⟩
    haveI : Subsingleton (A ⧸ P) := ⟨fun x y => by
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective P x
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective P y
      rw [(Submodule.Quotient.mk_eq_zero P).2 (htop ▸ Submodule.mem_top), (Submodule.Quotient.mk_eq_zero P).2 (htop ▸ Submodule.mem_top)]⟩
    exact ⟨equivOfSubsingleton _ _⟩
  ·
    obtain ⟨a₀, ha₀⟩ : ∃ a : A, a ∉ P := by
      by_contra h
      exact htop (eq_top_iff.2 fun a _ => not_not.1 (not_exists.1 h a))
    have hlt : Nat.card ↥P < n := hn ▸ Finite.card_subtype_lt ha₀

    set ρB := ρ.subrepresentation P h2 with hρB
    have h1B := torsionBy_le_comap ρB (p : ℤ)
    have h2B := smul_top_le_comap ρB (p : ℤ)
    obtain ⟨eB⟩ := ih _ hlt ↥P ρB h1B h2B rfl

    set ρT := ρ.subrepresentation T h1 with hρT
    set ρV := ρ.quotient P h2 with hρV

    set W₁ : Submodule ℤ T := P.comap T.subtype with hW₁def
    have hW₁ : ∀ g, W₁ ≤ W₁.comap (ρT g) := fun g x hx => h2 g hx

    set f := P.mkQ ∘ₗ T.subtype with hfdef
    have hf : ∀ g (t : T), f (ρT g t) = ρV g (f t) := fun g t => rfl
    have hkerf : LinearMap.ker f = W₁ := Submodule.ext fun x => by
      rw [LinearMap.mem_ker]
      exact Submodule.Quotient.mk_eq_zero P
    have hK₀ : ∀ g, LinearMap.range f ≤ (LinearMap.range f).comap (ρV g) := by
      rintro g _ ⟨t, rfl⟩
      exact ⟨ρT g t, hf g t⟩

    have hTp : ∀ t : T, p • t = 0 := fun t => by
      rw [← natCast_zsmul]
      exact Subtype.ext ((Submodule.mem_torsionBy_iff (p : ℤ) (t : A)).1 t.2)
    have hVp : ∀ x : A ⧸ P, p • x = 0 := fun x => by
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective P x
      rw [← Submodule.mkQ_apply, ← map_nsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hp0 a

    obtain ⟨C₁, hC₁, hcW⟩ := exists_isCompl_of_coprime hG ρT hTp W₁ hW₁
    obtain ⟨C₂, hC₂, hcK⟩ := exists_isCompl_of_coprime hG ρV hVp (LinearMap.range f) hK₀

    obtain ⟨e₂⟩ := nonempty_equiv_range_of_isCompl_ker ρT ρV f hf C₁ hC₁ (hkerf ▸ hcW) hK₀

    set PB : Submodule ℤ ↥P := (p : ℤ) • (⊤ : Submodule ℤ ↥P) with hPBdef
    have hmulP : P ≤ PB.comap (mulp p A) := fun a ha => by
      rw [Submodule.mem_comap]
      have : mulp p A a = (p : ℤ) • (⟨a, ha⟩ : ↥P) := Subtype.ext rfl
      rw [this]
      exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
    set gq := P.mapQ PB (mulp p A) hmulP with hgqdef
    have hmulρ : ∀ g (a : A), mulp p A (ρ g a) = ρB g (mulp p A a) := fun g a =>
      Subtype.ext (by change (p : ℤ) • ρ g a = ρ g ((p : ℤ) • a); rw [map_smul])
    have hgq : ∀ g (x : A ⧸ P), gq (ρV g x) = (ρB.quotient PB h2B) g (gq x) := fun g x => by
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective P x
      change gq (Submodule.Quotient.mk (ρ g a)) = (ρB.quotient PB h2B) g (Submodule.Quotient.mk (mulp p A a))
      change Submodule.Quotient.mk (mulp p A (ρ g a)) = Submodule.Quotient.mk (ρB g (mulp p A a))
      rw [hmulρ]
    have hgs : Function.Surjective gq := fun y => by
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective PB y
      obtain ⟨a, -, ha⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 b.2
      refine ⟨Submodule.Quotient.mk a, ?_⟩
      change Submodule.Quotient.mk (mulp p A a) = Submodule.Quotient.mk b
      congr 1
      exact Subtype.ext ha
    have hkerg : LinearMap.ker gq = LinearMap.range f := by
      apply le_antisymm
      · intro x hx
        obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective P x
        have hx' : Submodule.Quotient.mk (p := PB) (mulp p A a) = 0 := hx
        rw [Submodule.Quotient.mk_eq_zero] at hx'
        obtain ⟨b, -, hb⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx'
        have hb' : (p : ℤ) • (b : A) = (p : ℤ) • a := congrArg Subtype.val hb
        have hab : a - b ∈ T := by
          rw [Submodule.mem_torsionBy_iff, smul_sub, hb', sub_self]
        refine ⟨⟨a - b, hab⟩, ?_⟩
        change Submodule.Quotient.mk (p := P) (a - (b : A)) = Submodule.Quotient.mk a
        rw [Submodule.Quotient.mk_sub, (Submodule.Quotient.mk_eq_zero P).2 b.2, sub_zero]
      · rintro _ ⟨t, rfl⟩
        change Submodule.Quotient.mk (p := PB) (mulp p A (t : A)) = 0
        have : mulp p A (t : A) = 0 := Subtype.ext ((Submodule.mem_torsionBy_iff (p : ℤ) (t : A)).1 t.2)
        rw [this, Submodule.Quotient.mk_zero]

    obtain ⟨e₃⟩ := nonempty_equiv_of_isCompl_ker_of_surjective ρV (ρB.quotient PB h2B) gq hgq C₂ hC₂ (hkerg ▸ hcK) hgs

    have hTB : ∀ g, Submodule.torsionBy ℤ ↥P (p : ℤ) ≤ (Submodule.torsionBy ℤ ↥P (p : ℤ)).comap (ρB g) := h1B
    obtain ⟨e₁⟩ := nonempty_equiv_e₁ ρ h1 h2 hW₁ hTB

    exact nonempty_equiv_of_isCompl ρT ρV W₁ C₁ hW₁ hC₁ hcW C₂ (LinearMap.range f) hC₂ hK₀ hcK.symm
      (e₁.trans (eB.trans e₃.symm)) e₂

end Main

end TorsRed

theorem solution
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hG : (Nat.card G).Coprime p)
    {A : Type} [AddCommGroup A] [Finite A] (ρ : Representation ℤ G A)
    (h1 : ∀ g, Submodule.torsionBy ℤ A (p : ℤ) ≤ (Submodule.torsionBy ℤ A (p : ℤ)).comap (ρ g))
    (h2 : ∀ g, (p : ℤ) • (⊤ : Submodule ℤ A) ≤ ((p : ℤ) • (⊤ : Submodule ℤ A)).comap (ρ g)) :
    Nonempty ((ρ.subrepresentation _ h1).Equiv (ρ.quotient _ h2)) :=
  TorsRed.main hG _ A ρ h1 h2 rfl

end S_Representation_nonempty_equiv_torsionBy_quotient_of_coprime
end P2MW
export P2MW.S_Representation_nonempty_equiv_torsionBy_quotient_of_coprime (solution)
