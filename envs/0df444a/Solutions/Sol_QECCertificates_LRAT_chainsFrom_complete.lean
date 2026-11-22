-- Prove2me | solution 1 for QECCertificates.LRAT.chainsFrom_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:17:22.727947+00:00
-- url     : https://prove2.me/submissions/f797d428-d97e-4f93-9c4f-e41c30a5861e

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
public import Theorems.Thm_QECCertificates_LRAT_chainAssign_of_lt
public import Theorems.Thm_QECCertificates_LRAT_xorChainAux_complete
public import Theorems.Thm_QECCertificates_LRAT_xorChainAux_snd
public import Theorems.Thm_QECCertificates_LRAT_xorChainAux_vars_lt
public import Theorems.Thm_QECCertificates_LRAT_satClause_of_agree
public import Theorems.Thm_QECCertificates_LRAT_cntS_nil
public import Theorems.Thm_QECCertificates_LRAT_dotS_congr
public import Theorems.Thm_QECCertificates_LRAT_dotS_cons
public import Theorems.Thm_QECCertificates_LRAT_dotS_map
public import Theorems.Thm_QECCertificates_LRAT_dotS_nil
attribute [local simp] QECCertificates.LRAT.cntS_nil
attribute [local simp] QECCertificates.LRAT.dotS_cons
attribute [local simp] QECCertificates.LRAT.dotS_nil



set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT
namespace QECCertificates.LRAT
theorem _root_.solution {f : Nat → Nat} {rows : List (List Nat)}
    (hne : ∀ r ∈ rows, r ≠ []) :
    ∀ (c : Nat) (σ : Assign), (∀ r ∈ rows, ∀ t ∈ r, f t < c) →
      (∀ r ∈ rows, dotS (fun t => σ (f t)) r = false) →
      ∃ τ : Assign, (∀ t, t < c → τ t = σ t) ∧
        ∀ C ∈ (chainsFrom f rows c).1, SatClause τ C := by
  induction rows with
  | nil =>
      intro c σ _ _
      exact ⟨σ, fun _ _ => rfl, fun C hC => absurd hC (by simp [chainsFrom])⟩
  | cons r₀ rest ih =>
      intro c σ hlt hdot
      have hr₀ : r₀ ≠ [] := hne r₀ (List.mem_cons_self ..)
      have hrest_ne : ∀ r ∈ rest, r ≠ [] := fun r hr => hne r (List.mem_cons_of_mem _ hr)
      have hmap_ne : r₀.map f ≠ [] := fun h0 => hr₀ (List.map_eq_nil_iff.mp h0)
      obtain ⟨x₀, t, hmap⟩ : ∃ x₀ t, r₀.map f = x₀ :: t := by
        cases hm : r₀.map f with
        | nil => exact absurd hm hmap_ne
        | cons x₀ t => exact ⟨x₀, t, rfl⟩
      have hchain : xorChain (r₀.map f) false c = xorChainAux t false x₀ c := by
        simp only [xorChain, hmap]
      have hc' : (xorChain (r₀.map f) false c).2 = c + t.length := by
        rw [hchain, xorChainAux_snd]
      have hx₀ : x₀ < c := by
        obtain ⟨s, hs, hsf⟩ := List.mem_map.mp (by rw [hmap]; exact List.mem_cons_self ..)
        rw [← hsf]
        exact hlt r₀ (List.mem_cons_self ..) s hs
      have ht : ∀ s ∈ t, s < c := by
        intro s hs
        obtain ⟨s', hs', hsf⟩ := List.mem_map.mp (by rw [hmap]; exact List.mem_cons_of_mem _ hs)
        rw [← hsf]
        exact hlt r₀ (List.mem_cons_self ..) s' hs'
      have hdott : dotS σ (x₀ :: t) = false := by
        have h := hdot r₀ (List.mem_cons_self ..)
        rw [← dotS_map σ f r₀, hmap] at h
        exact h
      have hhead := xorChainAux_complete t false x₀ c σ hx₀ ht hdott
      have hlt' : ∀ r ∈ rest, ∀ s ∈ r, f s < c + t.length := by
        intro r hr s hs
        have := hlt r (List.mem_cons_of_mem _ hr) s hs
        omega
      have hdot' : ∀ r ∈ rest, dotS (fun s => chainAssign σ t (σ x₀) c (f s)) r = false := by
        intro r hr
        have h := hdot r (List.mem_cons_of_mem _ hr)
        have hfs : ∀ s ∈ r, f s < c := hlt r (List.mem_cons_of_mem _ hr)
        have hcongr : dotS (fun s => chainAssign σ t (σ x₀) c (f s)) r
            = dotS (fun s => σ (f s)) r :=
          dotS_congr (fun s hs => chainAssign_of_lt (hfs s hs))
        rw [hcongr]
        exact h
      obtain ⟨τ, hagree, hcl⟩ :=
        ih hrest_ne (c + t.length) (chainAssign σ t (σ x₀) c) hlt' hdot'
      refine ⟨τ, ?_, ?_⟩
      · intro s hs
        rw [hagree s (by omega : s < c + t.length), chainAssign_of_lt hs]
      · intro C hC
        simp only [chainsFrom, List.mem_append] at hC
        rcases hC with hC | hC
        · rw [hchain] at hC
          exact satClause_of_agree hagree
            (xorChainAux_vars_lt t false x₀ c hx₀ ht C hC) (hhead C hC)
        · rw [hc'] at hC
          exact hcl C hC
end QECCertificates.LRAT
