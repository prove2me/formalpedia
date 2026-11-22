-- Prove2me | solution 1 for QECCertificates.LRAT.xorChainAux_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:16:46.636699+00:00
-- url     : https://prove2.me/submissions/0f1ffcea-0537-436b-b80b-8ecb3965ae22

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
public import Theorems.Thm_QECCertificates_LRAT_chainAssign_of_lt
public import Theorems.Thm_QECCertificates_LRAT_chainAssign_self
public import Theorems.Thm_QECCertificates_LRAT_chainAssign_tail
public import Theorems.Thm_QECCertificates_LRAT_xorStepClauses_sat_of
public import Theorems.Thm_QECCertificates_LRAT_cntS_nil
public import Theorems.Thm_QECCertificates_LRAT_dotS_congr
public import Theorems.Thm_QECCertificates_LRAT_dotS_cons
public import Theorems.Thm_QECCertificates_LRAT_dotS_nil
attribute [local simp] QECCertificates.LRAT.cntS_nil
attribute [local simp] QECCertificates.LRAT.dotS_cons
attribute [local simp] QECCertificates.LRAT.dotS_nil



set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT
namespace QECCertificates.LRAT
theorem _root_.solution : ∀ (rest : List Nat) (want : Bool) (cur c : Nat) (σ : Assign),
    cur < c → (∀ t ∈ rest, t < c) → dotS σ (cur :: rest) = want →
    ∀ C ∈ (xorChainAux rest want cur c).1, SatClause (chainAssign σ rest (σ cur) c) C := by
  intro rest
  induction rest with
  | nil =>
      intro want cur c σ hcur _ hd C hC
      simp only [xorChainAux, List.mem_cons, List.not_mem_nil, or_false] at hC
      rcases hC with rfl
      refine ⟨(cur, want), List.mem_cons_self .., ?_⟩
      have hcw : σ cur = want := by
        simpa only [dotS_cons, dotS_nil, Bool.xor_false] using hd
      rw [chainAssign_of_lt hcur, hcw]
  | cons x rest ih =>
      intro want cur c σ hcur hrest hd
      have hx : x < c := hrest x (List.mem_cons_self ..)
      have hrest' : ∀ t ∈ rest, t < c + 1 := fun t ht => by
        have h := hrest t (List.mem_cons_of_mem _ ht); omega
      have hc1 : c < c + 1 := by omega
      have hstep : ∀ C ∈ xorStepClauses cur x c,
          SatClause (chainAssign σ (x :: rest) (σ cur) c) C := by
        refine xorStepClauses_sat_of ?_
        rw [chainAssign_self, chainAssign_of_lt hcur, chainAssign_of_lt hx]
      have hd' : dotS (chainAssign σ (x :: rest) (σ cur) c) (c :: rest) = want := by
        rw [dotS_cons, chainAssign_self]
        have hcongr : dotS (chainAssign σ (x :: rest) (σ cur) c) rest = dotS σ rest :=
          dotS_congr (fun t ht => chainAssign_of_lt (hrest t (List.mem_cons_of_mem _ ht)))
        rw [hcongr]
        rw [dotS_cons, dotS_cons] at hd
        rw [← hd, Bool.xor_assoc]
      have htail : ∀ C ∈ (xorChainAux rest want c (c + 1)).1,
          SatClause (chainAssign σ (x :: rest) (σ cur) c) C := by
        have htail' := ih want c (c + 1) (chainAssign σ (x :: rest) (σ cur) c) hc1 hrest' hd'
        intro C hC
        have h2 := htail' C hC
        -- Rewrite the function argument using extensional equality, not pointwise equalities.
        have hfun : chainAssign (chainAssign σ (x :: rest) (σ cur) c) rest
              (chainAssign σ (x :: rest) (σ cur) c c) (c + 1)
            = chainAssign σ (x :: rest) (σ cur) c :=
          funext (chainAssign_tail σ x rest (σ cur) c
            (fun t ht => hrest t (List.mem_cons_of_mem _ ht)))
        rwa [hfun] at h2
      intro C hC
      simp only [xorChainAux, List.mem_append] at hC
      rcases hC with hC | hC
      · exact hstep C hC
      · exact htail C hC
end QECCertificates.LRAT
