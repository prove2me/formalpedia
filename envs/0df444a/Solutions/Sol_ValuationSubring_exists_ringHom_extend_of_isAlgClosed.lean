-- Prove2me | solution 1 for ValuationSubring.exists_ringHom_extend_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/bc37b9a6-61b9-5ce2-975b-87153086d557

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_ringHom_extend_of_isAlgClosed

set_option autoImplicit false

namespace ChevalleyHom

variable {L Ω : Type*} [Field L] [Field Ω]

def IsGraph (Γ : Subring (L × Ω)) : Prop := ∀ a : Ω, ((0 : L), a) ∈ Γ → a = 0

namespace IsGraph

variable {Γ : Subring (L × Ω)}

theorem snd_eq (hΓ : IsGraph Γ) {x : L} {a b : Ω} (ha : (x, a) ∈ Γ) (hb : (x, b) ∈ Γ) : a = b := by
  have h := Γ.sub_mem ha hb
  rw [Prod.mk_sub_mk, sub_self] at h
  exact sub_eq_zero.mp (hΓ _ h)

theorem fst_ne_zero (hΓ : IsGraph Γ) {x : L} {a : Ω} (h : (x, a) ∈ Γ) (ha : a ≠ 0) : x ≠ 0 := by
  rintro rfl; exact ha (hΓ a h)

def dom (Γ : Subring (L × Ω)) : Subring L := Γ.map (RingHom.fst L Ω)

theorem mem_dom {x : L} : x ∈ dom Γ ↔ ∃ a, (x, a) ∈ Γ := by
  simp only [dom, Subring.mem_map, RingHom.coe_fst, Prod.exists, exists_and_right, exists_eq_right]

noncomputable def fn (Γ : Subring (L × Ω)) (x : L) : Ω :=
  open Classical in if h : ∃ a, (x, a) ∈ Γ then Classical.choose h else 0

theorem fn_spec (hΓ : IsGraph Γ) {x : L} {a : Ω} (h : (x, a) ∈ Γ) : fn Γ x = a := by
  unfold fn
  rw [dif_pos ⟨a, h⟩]
  exact hΓ.snd_eq (Classical.choose_spec (⟨a, h⟩ : ∃ a, (x, a) ∈ Γ)) h

theorem mem_of_mem_dom {x : L} (hx : x ∈ dom Γ) : (x, fn Γ x) ∈ Γ := by
  obtain ⟨a, ha⟩ := mem_dom.mp hx
  unfold fn
  rw [dif_pos ⟨a, ha⟩]
  exact Classical.choose_spec (⟨a, ha⟩ : ∃ a, (x, a) ∈ Γ)

noncomputable def hom (hΓ : IsGraph Γ) : dom Γ →+* Ω where
  toFun x := fn Γ x
  map_one' := hΓ.fn_spec Γ.one_mem
  map_mul' x y := hΓ.fn_spec (by simpa using Γ.mul_mem (mem_of_mem_dom x.2) (mem_of_mem_dom y.2))
  map_zero' := hΓ.fn_spec Γ.zero_mem
  map_add' x y := hΓ.fn_spec (by simpa using Γ.add_mem (mem_of_mem_dom x.2) (mem_of_mem_dom y.2))

theorem hom_apply (hΓ : IsGraph Γ) (x : dom Γ) : hΓ.hom x = fn Γ x := rfl

theorem hom_eq_of_mem (hΓ : IsGraph Γ) {x : L} {a : Ω} (h : (x, a) ∈ Γ) :
    hΓ.hom ⟨x, mem_dom.mpr ⟨a, h⟩⟩ = a := hΓ.fn_spec h

end IsGraph

def graph (R : Subring L) (φ : R →+* Ω) : Subring (L × Ω) :=
  ((R.subtype).prod (φ)).range.copy {p | ∃ h : p.1 ∈ R, φ ⟨p.1, h⟩ = p.2} (by
    ext ⟨x, a⟩
    simp only [Set.mem_setOf_eq, RingHom.coe_range, Set.mem_range, RingHom.prod_apply, Prod.mk.injEq,
      Subring.coe_subtype]
    constructor
    · rintro ⟨h, ha⟩; exact ⟨⟨x, h⟩, rfl, ha⟩
    · rintro ⟨⟨y, hy⟩, rfl, rfl⟩; exact ⟨hy, rfl⟩)

theorem mem_graph {R : Subring L} {φ : R →+* Ω} {p : L × Ω} :
    p ∈ graph R φ ↔ ∃ h : p.1 ∈ R, φ ⟨p.1, h⟩ = p.2 := Iff.rfl

theorem isGraph_graph (R : Subring L) (φ : R →+* Ω) : IsGraph (graph R φ) := by
  rintro a ⟨h, ha⟩
  have h0 : (⟨(((0 : L), a) : L × Ω).1, h⟩ : R) = 0 := Subtype.ext rfl
  rw [h0, map_zero] at ha
  exact ha.symm

end ChevalleyHom

namespace ChevalleyHom

variable {L Ω : Type*} [Field L] [Field Ω]

def Above (Γ₀ : Subring (L × Ω)) : Set (Subring (L × Ω)) := {Γ | Γ₀ ≤ Γ ∧ IsGraph Γ}

theorem exists_maximal (Γ₀ : Subring (L × Ω)) (h₀ : IsGraph Γ₀) :
    ∃ Γ, Γ₀ ≤ Γ ∧ Maximal (· ∈ Above Γ₀) Γ := by
  refine zorn_le_nonempty₀ (Above Γ₀) (fun c hc hchain y hy => ?_) Γ₀ ⟨le_rfl, h₀⟩
  haveI : Nonempty c := ⟨⟨y, hy⟩⟩
  have hdir : Directed (· ≤ ·) (fun Γ : c => (Γ : Subring (L × Ω))) :=
    hchain.directedOn.directed_val
  refine ⟨⨆ Γ : c, (Γ : Subring (L × Ω)), ⟨?_, ?_⟩, fun z hz => le_iSup (fun Γ : c => (Γ : Subring (L × Ω))) ⟨z, hz⟩⟩
  · exact (hc hy).1.trans (le_iSup (fun Γ : c => (Γ : Subring (L × Ω))) ⟨y, hy⟩)
  · intro a ha
    obtain ⟨Γ, hΓ⟩ := (Subring.mem_iSup_of_directed hdir).mp ha
    exact (hc Γ.2).2 a hΓ

section Maximal

variable {Γ₀ Γ : Subring (L × Ω)} (hmax : Maximal (· ∈ Above Γ₀) Γ)
include hmax

theorem isGraph_of_maximal : IsGraph Γ := hmax.prop.2

theorem le_of_maximal : Γ₀ ≤ Γ := hmax.prop.1

theorem eq_of_le (Γ' : Subring (L × Ω)) (hΓ' : IsGraph Γ') (hle : Γ ≤ Γ') : Γ' = Γ :=
  (hmax.eq_of_ge ⟨hmax.prop.1.trans hle, hΓ'⟩ hle)

theorem inv_mem {x : L} {a : Ω} (h : (x, a) ∈ Γ) (ha : a ≠ 0) : (x⁻¹, a⁻¹) ∈ Γ := by
  have hΓ := isGraph_of_maximal hmax

  let Γ' : Subring (L × Ω) :=
    { carrier := {q | ∃ p ∈ Γ, ∃ s ∈ Γ, s.2 ≠ 0 ∧ q = (p.1 / s.1, p.2 / s.2)}
      mul_mem' := by
        rintro _ _ ⟨p, hp, s, hs, hs0, rfl⟩ ⟨p', hp', s', hs', hs0', rfl⟩
        refine ⟨p * p', Γ.mul_mem hp hp', s * s', Γ.mul_mem hs hs', mul_ne_zero hs0 hs0', ?_⟩
        ext <;> simp [div_mul_div_comm]
      one_mem' := ⟨1, Γ.one_mem, 1, Γ.one_mem, one_ne_zero, by ext <;> simp⟩
      add_mem' := by
        rintro _ _ ⟨p, hp, s, hs, hs0, rfl⟩ ⟨p', hp', s', hs', hs0', rfl⟩
        have hs1 : s.1 ≠ 0 := hΓ.fst_ne_zero (by simpa using hs) hs0
        have hs1' : s'.1 ≠ 0 := hΓ.fst_ne_zero (by simpa using hs') hs0'
        refine ⟨p * s' + p' * s, Γ.add_mem (Γ.mul_mem hp hs') (Γ.mul_mem hp' hs), s * s',
          Γ.mul_mem hs hs', mul_ne_zero hs0 hs0', ?_⟩
        ext
        · simp only [Prod.fst_add, Prod.fst_mul]; rw [div_add_div _ _ hs1 hs1']; ring
        · simp only [Prod.snd_add, Prod.snd_mul]; rw [div_add_div _ _ hs0 hs0']; ring
      zero_mem' := ⟨0, Γ.zero_mem, 1, Γ.one_mem, one_ne_zero, by ext <;> simp⟩
      neg_mem' := by
        rintro _ ⟨p, hp, s, hs, hs0, rfl⟩
        exact ⟨-p, Γ.neg_mem hp, s, hs, hs0, by ext <;> simp [neg_div]⟩ }
  have hle : Γ ≤ Γ' := fun p hp => ⟨p, hp, 1, Γ.one_mem, one_ne_zero, by simp⟩
  have hΓ' : IsGraph Γ' := by
    rintro b ⟨p, hp, s, hs, hs0, hq⟩
    simp only [Prod.mk.injEq] at hq
    obtain ⟨h1, h2⟩ := hq
    have hs1 : s.1 ≠ 0 := hΓ.fst_ne_zero (by simpa using hs) hs0
    have hp1 : p.1 = 0 := by
      rcases div_eq_zero_iff.mp h1.symm with h | h
      · exact h
      · exact absurd h hs1
    have hp2 : p.2 = 0 := hΓ p.2 (by rwa [← hp1])
    rw [h2, hp2, zero_div]
  have heq := eq_of_le hmax Γ' hΓ' hle
  have : (x⁻¹, a⁻¹) ∈ Γ' := ⟨1, Γ.one_mem, (x, a), h, ha, by ext <;> simp⟩
  rwa [heq] at this

theorem isUnit_iff {x : IsGraph.dom Γ} : IsUnit x ↔ (isGraph_of_maximal hmax).hom x ≠ 0 := by
  have hΓ := isGraph_of_maximal hmax
  constructor
  · intro hu h0
    have := hu.map hΓ.hom
    rw [h0] at this
    exact not_isUnit_zero this
  · intro hne
    have hmem : ((x : L), IsGraph.fn Γ x) ∈ Γ := IsGraph.mem_of_mem_dom x.2
    have hinv := inv_mem hmax hmem hne
    have hx0 : (x : L) ≠ 0 := hΓ.fst_ne_zero hmem hne
    refine ⟨⟨x, ⟨(x : L)⁻¹, IsGraph.mem_dom.mpr ⟨_, hinv⟩⟩, ?_, ?_⟩, rfl⟩
    · exact Subtype.ext (mul_inv_cancel₀ hx0)
    · exact Subtype.ext (inv_mul_cancel₀ hx0)

theorem isLocalRing : IsLocalRing (IsGraph.dom Γ) := by
  have hΓ := isGraph_of_maximal hmax
  haveI : Nontrivial (IsGraph.dom Γ) := inferInstance
  refine IsLocalRing.of_nonunits_add fun a b ha hb => ?_
  rw [mem_nonunits_iff, isUnit_iff hmax, not_not] at ha hb ⊢
  rw [map_add, ha, hb, add_zero]

theorem mem_maximalIdeal_iff (x : IsGraph.dom Γ) :
    haveI := isLocalRing hmax
    x ∈ IsLocalRing.maximalIdeal (IsGraph.dom Γ) ↔ (isGraph_of_maximal hmax).hom x = 0 := by
  haveI := isLocalRing hmax
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff hmax, not_not]

end Maximal

end ChevalleyHom

namespace ChevalleyHom

variable {L Ω : Type*} [Field L] [Field Ω]

section Extend

variable {Γ₀ Γ : Subring (L × Ω)} (hmax : Maximal (· ∈ Above Γ₀) Γ)
include hmax

open IsGraph Polynomial in

theorem mem_dom_of_hom [IsAlgClosed Ω] (z : L) {F : Type*} [Field F]
    (θ : Polynomial (dom Γ) →+* F)
    (hθm : haveI := isLocalRing hmax; ∀ b ∈ IsLocalRing.maximalIdeal (dom Γ), θ (C b) = 0)
    (hθz : ∀ p : Polynomial (dom Γ), aeval z p = 0 → θ p = 0) :
    z ∈ dom Γ := by
  classical
  haveI := isLocalRing hmax
  have hΓ := isGraph_of_maximal hmax

  let B := dom Γ
  let m := IsLocalRing.maximalIdeal B
  let k := B ⧸ m
  letI : Field k := Ideal.Quotient.field m
  let π : Polynomial B →+* Polynomial k := mapRingHom (Ideal.Quotient.mk m)
  have hπ : Function.Surjective π := map_surjective _ Ideal.Quotient.mk_surjective
  let ev : Polynomial B →+* L := (aeval z : Polynomial B →ₐ[B] L).toRingHom
  let K₀ : Ideal (Polynomial B) := RingHom.ker ev
  let Jk : Ideal (Polynomial k) := K₀.map π

  have hθker : ∀ q, π q = 0 → θ q = 0 := by
    intro q hq
    have hq' : q ∈ RingHom.ker π := hq
    rw [ker_mapRingHom, Ideal.mk_ker] at hq'
    have hle : Ideal.map (C : B →+* Polynomial B) m ≤ RingHom.ker θ :=
      Ideal.map_le_iff_le_comap.mpr fun b hb => Ideal.mem_comap.mpr (RingHom.mem_ker.mpr (hθm b hb))
    exact hle hq'

  have hJk : Jk ≠ ⊤ := by
    intro htop
    have h1 : (1 : Polynomial k) ∈ Jk := htop ▸ Submodule.mem_top
    obtain ⟨q, hq, hq1⟩ := (Ideal.mem_map_iff_of_surjective π hπ).mp h1
    have hq0 : θ q = 0 := hθz q hq
    have h1q : θ (1 - q) = 0 := hθker _ (by rw [map_sub, map_one, hq1, sub_self])
    rw [map_sub, map_one, hq0, sub_zero] at h1q
    exact one_ne_zero h1q

  obtain ⟨h, hh⟩ := (IsPrincipalIdealRing.principal Jk).principal
  have hhu : ¬ IsUnit h := fun hu => hJk (by rw [hh, Ideal.submodule_span_eq, Ideal.span_singleton_eq_top]; exact hu)
  have hker : ∀ b ∈ m, hΓ.hom b = 0 := fun b hb => (mem_maximalIdeal_iff hmax b).mp hb
  let ι : k →+* Ω := Ideal.Quotient.lift m hΓ.hom hker
  obtain ⟨ω, hω⟩ : ∃ ω : Ω, (h.map ι).eval ω = 0 := by
    by_cases h0 : h = 0
    · exact ⟨0, by simp [h0]⟩
    · have hdeg : (h.map ι).degree ≠ 0 := by
        rw [degree_map]
        exact fun hd => hhu (isUnit_iff_degree_eq_zero.mpr hd)
      obtain ⟨ω, hω⟩ := IsAlgClosed.exists_root (h.map ι) hdeg
      exact ⟨ω, hω⟩

  let G : Polynomial B →+* Ω := eval₂RingHom (ι.comp (Ideal.Quotient.mk m)) ω
  have hG : ∀ q ∈ K₀, G q = 0 := by
    intro q hq
    have hπq : π q ∈ Jk := Ideal.mem_map_of_mem π hq
    rw [hh, Ideal.submodule_span_eq, Ideal.mem_span_singleton] at hπq
    obtain ⟨r, hr⟩ := hπq
    have : G q = (π q).eval₂ ι ω := by
      simp only [G, π, coe_eval₂RingHom, coe_mapRingHom, eval₂_map]
    rw [this, hr, eval₂_mul, ← eval_map, hω, zero_mul]

  let S : Subring L := ev.range
  let e := RingHom.quotientKerEquivRange ev
  let g' : S →+* Ω := (Ideal.Quotient.lift K₀ G hG).comp e.symm.toRingHom
  have hg' : ∀ q : Polynomial B, g' ⟨ev q, ⟨q, rfl⟩⟩ = G q := by
    intro q
    have he : e (Ideal.Quotient.mk K₀ q) = ⟨ev q, ⟨q, rfl⟩⟩ := rfl
    show (Ideal.Quotient.lift K₀ G hG) (e.symm ⟨ev q, ⟨q, rfl⟩⟩) = G q
    rw [← he, RingEquiv.symm_apply_apply, Ideal.Quotient.lift_mk]

  let Γ' : Subring (L × Ω) := (S.subtype.prod g').range
  have hΓ' : IsGraph Γ' := by
    rintro a ⟨s, hs⟩
    simp only [RingHom.prod_apply, Prod.mk.injEq, Subring.coe_subtype] at hs
    obtain ⟨hs1, hs2⟩ := hs
    have : s = 0 := Subtype.ext hs1
    rw [← hs2, this, map_zero]
  have evC : ∀ b : B, ev (C b) = (b : L) := fun b => by
    show aeval z (C b) = (b : L)
    rw [aeval_C]
    rfl
  have hle : Γ ≤ Γ' := by
    rintro ⟨x, a⟩ hxa
    have hx : x ∈ B := mem_dom.mpr ⟨a, hxa⟩
    have hmemS : x ∈ S := ⟨C ⟨x, hx⟩, evC ⟨x, hx⟩⟩
    refine ⟨⟨x, hmemS⟩, ?_⟩
    simp only [RingHom.prod_apply, Prod.mk.injEq, Subring.coe_subtype, true_and]
    have h1 : g' ⟨x, hmemS⟩ = G (C ⟨x, hx⟩) := by
      have h2 := hg' (C ⟨x, hx⟩)
      have h3 : (⟨ev (C ⟨x, hx⟩), ⟨C ⟨x, hx⟩, rfl⟩⟩ : S) = ⟨x, hmemS⟩ := Subtype.ext (evC ⟨x, hx⟩)
      rw [h3] at h2
      exact h2
    rw [h1]
    simp only [G, coe_eval₂RingHom, eval₂_C, RingHom.comp_apply]
    show ι (Ideal.Quotient.mk m ⟨x, hx⟩) = a
    rw [Ideal.Quotient.lift_mk]
    exact hΓ.hom_eq_of_mem hxa
  have heq := eq_of_le hmax Γ' hΓ' hle
  have evX : ev X = z := by show aeval z (X : Polynomial B) = z; exact aeval_X z
  have hz : ((z, g' ⟨z, ⟨X, evX⟩⟩) : L × Ω) ∈ Γ' := ⟨⟨z, ⟨X, evX⟩⟩, rfl⟩
  rw [heq] at hz
  exact mem_dom.mpr ⟨_, hz⟩

end Extend

open IsGraph Polynomial in
theorem main [IsAlgClosed Ω] (R : Subring L) (φ : R →+* Ω) :
    ∃ (O : ValuationSubring L) (h : R ≤ O.toSubring) (ψ : O →+* Ω),
      ψ.comp (Subring.inclusion h) = φ ∧ RingHom.ker ψ = IsLocalRing.maximalIdeal O := by
  classical
  obtain ⟨Γ, -, hmax⟩ := exists_maximal (graph R φ) (isGraph_graph R φ)
  have hΓ := isGraph_of_maximal hmax
  haveI := isLocalRing hmax
  let B := dom Γ

  obtain ⟨V, hV⟩ := LocalSubring.exists_le_valuationSubring (LocalSubring.mk B : LocalSubring L)
  obtain ⟨hBV, hloc⟩ := LocalSubring.le_def.mp hV

  have key : ∀ z : L, z ∈ V → z ∈ B := by
    intro z hz
    let incl : B →+* V := Subring.inclusion hBV
    haveI : IsLocalHom incl := hloc
    let θ : Polynomial B →+* IsLocalRing.ResidueField V :=
      (IsLocalRing.residue V).comp (eval₂RingHom incl ⟨z, hz⟩)
    refine mem_dom_of_hom hmax z θ (fun b hb => ?_) (fun p hp => ?_)
    · simp only [θ, RingHom.comp_apply, coe_eval₂RingHom, eval₂_C, IsLocalRing.residue_eq_zero_iff]
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hb ⊢
      exact fun hu => hb (IsUnit.of_map incl _ hu)
    · simp only [θ, RingHom.comp_apply, coe_eval₂RingHom]
      have hval : (V.subtype) (eval₂ incl ⟨z, hz⟩ p) = aeval z p := by
        rw [hom_eval₂]
        rfl
      have : eval₂ incl ⟨z, hz⟩ p = 0 := by
        apply Subtype.val_injective
        show (V.subtype) (eval₂ incl ⟨z, hz⟩ p) = ((0 : V) : L)
        rw [hval, hp]
        rfl
      rw [this, map_zero]
  have hval : ∀ z : L, z ∈ B ∨ z⁻¹ ∈ B := fun z =>
    (V.mem_or_inv_mem z).imp (key z) (key z⁻¹)
  let O : ValuationSubring L := { toSubring := B, mem_or_inv_mem' := hval }
  have hR : R ≤ O.toSubring := fun r hr => mem_dom.mpr ⟨φ ⟨r, hr⟩, mem_graph.mpr ⟨hr, rfl⟩ |> le_of_maximal hmax⟩
  refine ⟨O, hR, hΓ.hom, ?_, ?_⟩
  · ext r
    exact hΓ.hom_eq_of_mem (le_of_maximal hmax (mem_graph.mpr ⟨r.2, rfl⟩))
  · ext x
    rw [RingHom.mem_ker]
    exact (mem_maximalIdeal_iff hmax x).symm

end ChevalleyHom

theorem solution
    {L Ω : Type*} [Field L] [Field Ω] [IsAlgClosed Ω] (R : Subring L) (φ : R →+* Ω) :
    ∃ (O : ValuationSubring L) (h : R ≤ O.toSubring) (ψ : O →+* Ω),
      ψ.comp (Subring.inclusion h) = φ ∧ RingHom.ker ψ = IsLocalRing.maximalIdeal O :=
  ChevalleyHom.main R φ

end S_ValuationSubring_exists_ringHom_extend_of_isAlgClosed
end P2MW
export P2MW.S_ValuationSubring_exists_ringHom_extend_of_isAlgClosed (solution)
