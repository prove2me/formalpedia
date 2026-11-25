-- Prove2me | solution 1 for UpperTheory.Reformulated.B.AdmissibleSchurLemma.schur_adm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:02:23.553286+00:00
-- url     : https://prove2.me/submissions/49fd35de-85c4-4f87-b407-55edb025cd5b

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_AdmissibleSchurLemma
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
private theorem UpperTheory.Reformulated.B.AdmissibleSchurLemma.mem_fixed_iff {k G V : Type} [Field k] [Group G] [AddCommGroup V]
    [_root_.Module k V] (ρ : Representation k G V) (H : Subgroup G) (v : V) :
    v ∈ UpperTheory.Reformulated.B.AdmissibleSchurLemma.fixed ρ H ↔ ∀ g ∈ H, ρ g v = v := by
  change (∀ h : H, ρ (h : G) v = (((1 : H →* kˣ) h : kˣ) : k) • v) ↔ _
  simp
end

set_option autoImplicit false

namespace UpperTheory.Reformulated.B.AdmissibleSchurLemma
theorem _root_.solution :
    ∀ (G : Type) [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G),
      IsOpen (↑K : Set G) →
        IsCompact (↑K : Set G) →
          ∀ (N : Type) [inst_3 : AddCommGroup N] [inst_4 : _root_.Module ℂ N] (π : Representation ℂ G N),
            π.IsIrreducible →
              UpperTheory.Reformulated.B.AdmissibleSchurLemma.IsAdmissible π →
                ∀ (φ : N →ₗ[ℂ] N),
                  (∀ (g : G) (x : N),
                      (φ : N → N) (((π : G → N →ₗ[ℂ] N) g : N → N) x) = ((π : G → N →ₗ[ℂ] N) g : N → N) ((φ : N → N) x)) →
                    ∃ (c : ℂ), φ = c • LinearMap.id := by
  intro G _ _ _ K hKo hKc N _ _ π hirr hadm φ hφ
  obtain ⟨hsm, hfd⟩ := hadm
  rcases subsingleton_or_nontrivial N with hN | hN
  · exact ⟨0, Subsingleton.elim _ _⟩
  obtain ⟨v, hv⟩ := exists_ne (0 : N)
  let S : Subgroup G :=
    { carrier := {g | π g v = v}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        have ha' : π a v = v := ha
        have hb' : π b v = v := hb
        change π (a * b) v = v
        rw [map_mul, Module.End.mul_apply, hb', ha']
      inv_mem' := by
        intro a ha
        have ha' : π a v = v := ha
        change π a⁻¹ v = v
        calc π a⁻¹ v = π a⁻¹ (π a v) := by rw [ha']
          _ = v := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
              Module.End.one_apply] }
  have hSo : IsOpen (S : Set G) := hsm v
  have hSc : IsClosed (S : Set G) := S.isClosed_of_isOpen hSo
  have hfin : FiniteDimensional ℂ (UpperTheory.Reformulated.B.AdmissibleSchurLemma.fixed π (K ⊓ S)) :=
    hfd (K ⊓ S) (hKo.inter hSo) (hKc.inter_right hSc)
  have hvU : v ∈ UpperTheory.Reformulated.B.AdmissibleSchurLemma.fixed π (K ⊓ S) :=
    (UpperTheory.Reformulated.B.AdmissibleSchurLemma.mem_fixed_iff π _ v).2 fun g hg => hg.2
  have hnt : Nontrivial (UpperTheory.Reformulated.B.AdmissibleSchurLemma.fixed π (K ⊓ S)) :=
    ⟨⟨⟨v, hvU⟩, 0, fun h => hv (congrArg Subtype.val h)⟩⟩
  have hst : ∀ x ∈ UpperTheory.Reformulated.B.AdmissibleSchurLemma.fixed π (K ⊓ S), φ x ∈ UpperTheory.Reformulated.B.AdmissibleSchurLemma.fixed π (K ⊓ S) := by
    intro x hx
    rw [UpperTheory.Reformulated.B.AdmissibleSchurLemma.mem_fixed_iff] at hx ⊢
    intro g hg
    rw [← hφ, hx g hg]
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (φ.restrict hst)
  obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
  have hw0 : (w : N) ≠ 0 := fun h => hw.2 (Subtype.ext h)
  have hwc : φ w = c • (w : N) := congrArg Subtype.val hw.apply_eq_smul
  let E : Subrepresentation π :=
    { toSubmodule := Module.End.eigenspace φ c
      apply_mem_toSubmodule := by
        intro g x hx
        rw [Module.End.mem_eigenspace_iff] at hx ⊢
        rw [hφ, hx, map_smul] }
  refine ⟨c, ?_⟩
  rcases hirr.eq_bot_or_eq_top E with hE | hE
  · have h1 : Module.End.eigenspace φ c = ⊥ := congrArg Subrepresentation.toSubmodule hE
    have h2 : (w : N) ∈ Module.End.eigenspace φ c := Module.End.mem_eigenspace_iff.2 hwc
    rw [h1] at h2
    exact absurd ((Submodule.mem_bot ℂ).1 h2) hw0
  · have h1 : Module.End.eigenspace φ c = ⊤ := congrArg Subrepresentation.toSubmodule hE
    ext x
    have h2 : x ∈ Module.End.eigenspace φ c := h1 ▸ Submodule.mem_top
    simpa using Module.End.mem_eigenspace_iff.1 h2
end UpperTheory.Reformulated.B.AdmissibleSchurLemma
